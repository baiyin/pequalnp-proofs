import Mathlib
import PEqualNP.Outside.L_meta_534
import PEqualNP.MetaComplexity.Helpers.Support

/-! A local follow-up to L-meta-1745. A gate is counted at most once per
wire, even if it lists the same wire twice. Only ports actually read by
the operation count, exactly as in the posted problem. -/

namespace PEqualNP.Research.ReaderBudget1745

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.Helpers

def effectiveInputs (g : Gate) : List ℕ :=
  g.inputs.take (bif g.op.eval [false] then 1 else 2)

theorem effective_eval (g : Gate) (ok : FanInTwo ⟨[g],0⟩) (f : ℕ → Bool) :
    g.op.eval (g.inputs.map f) = g.op.eval ((effectiveInputs g).map f) := by
  obtain ⟨hop, hlen⟩ := ok g (by simp)
  rcases hop with hand | hor | hnot
  · simp [effectiveInputs, hand, GateOp.eval, List.take_of_length_le hlen]
  · simp [effectiveInputs, hor, GateOp.eval, List.take_of_length_le hlen]
  · change g.op = GateOp.not at hnot
    cases h : g.inputs <;> simp [effectiveInputs, hnot, GateOp.eval, h]

def readers (gs : List Gate) (wire : ℕ) : ℕ :=
  (gs.filter fun g => (effectiveInputs g).contains wire).length

private theorem ports (gs : List Gate) (U : Finset ℕ)
    (fan : ∀ g ∈ gs, g.inputs.length ≤ 2) :
    ∑ i ∈ U, readers gs i ≤ 2 * gs.length := by
  classical
  induction gs with
  | nil => simp [readers]
  | cons g gs ih =>
    have head (i : ℕ) : readers (g :: gs) i =
        (if i ∈ effectiveInputs g then 1 else 0) + readers gs i := by
      by_cases h : i ∈ effectiveInputs g <;> simp [readers, h, Nat.add_comm]
    have hsub : U.filter (· ∈ effectiveInputs g) ⊆ (effectiveInputs g).toFinset := by simp [Finset.subset_iff]
    have hcount := (Finset.card_le_card hsub).trans (effectiveInputs g).toFinset_card_le
    have htake : (effectiveInputs g).length ≤ g.inputs.length := by simp [effectiveInputs]
    have hgate := fan g (by simp)
    have htail := ih (fun a ha => fan a (by simp [ha]))
    simp only [head, Finset.sum_add_distrib, Finset.sum_boole, Nat.cast_id, List.length_cons]
    omega

/-- All but the last gate must feed another gate. Counting those wires leaves
at most one more input-to-gate incidence than the number of gates. -/
theorem input_budget {n : ℕ} {C : Circuit} (least : IsMinimalCircuit n C)
    (nc : ∃ x y, circuitFun n C x ≠ circuitFun n C y) :
    ∑ i : Fin n, readers C.gates i.val ≤ C.size + 1 := by
  have live := (PEqualNP.Outside.L_meta_534 n C least nc).2.2.2
  have used (j : ℕ) (hj : j ∈ Finset.range (C.gates.length - 1)) :
      1 ≤ readers C.gates (n + j) := by
    have hj' := Finset.mem_range.mp hj
    obtain ⟨⟨g,k⟩, hg, _, hread⟩ := live j (by omega)
    apply List.length_filter_pos_iff.mpr
    refine ⟨g, List.fst_mem_of_mem_zipIdx hg, ?_⟩
    apply List.contains_iff_mem.mpr
    have hm := List.contains_iff_mem.mp hread
    have hg' : g ∈ C.gates := List.fst_mem_of_mem_zipIdx hg
    obtain ⟨hop, hlen⟩ := least.1 g hg'
    rcases hop with hand | hor | hnot
    · simpa [effectiveInputs, hand, GateOp.eval, List.take_of_length_le hlen] using hm
    · simpa [effectiveInputs, hor, GateOp.eval, List.take_of_length_le hlen] using hm
    · change g.op = GateOp.not at hnot
      simpa [effectiveInputs, hnot, GateOp.eval] using hm
  have hmin := Finset.sum_le_sum used
  simp only [Finset.sum_const, Finset.card_range, smul_eq_mul, mul_one] at hmin
  have h := ports C.gates (Finset.range (n + (C.gates.length - 1)))
    (fun g hg => (least.1 g hg).2)
  rw [Finset.sum_range_add, ← Fin.sum_univ_eq_sum_range] at h
  unfold Circuit.size
  omega

private theorem agree_except (gs : List Gate) (a : ℕ)
    (fan : ∀ g ∈ gs, FanInTwo ⟨[g],0⟩)
    (unread : ∀ g ∈ gs, a ∉ effectiveInputs g) (x y : List Bool)
    (len : x.length = y.length) (off : ∀ i, i ≠ a → x.getD i false = y.getD i false) :
    ∀ i, i ≠ a → (wiresFrom gs x).getD i false = (wiresFrom gs y).getD i false := by
  induction gs generalizing x y with
  | nil => exact off
  | cons g gs ih =>
    have same : (effectiveInputs g).map (fun i => x.getD i false) =
        (effectiveInputs g).map (fun i => y.getD i false) := by
      apply List.map_congr_left
      intro i hi
      exact off i (fun eq => unread g (by simp) (eq ▸ hi))
    have eqGate : g.op.eval (g.inputs.map (fun i => x.getD i false)) =
        g.op.eval (g.inputs.map (fun i => y.getD i false)) := by
      simp only [effective_eval g (fan g (by simp)), same]
    simp only [wiresFrom, List.foldl_cons] at ih ⊢
    rw [eqGate]
    apply ih (fun g hg => fan g (by simp [hg])) (fun g hg => unread g (by simp [hg]))
    · simp [len]
    · intro i hia
      by_cases h : i = x.length
      · subst i
        simp [len]
      · rw [getD_snoc_ne _ _ _ _ h, getD_snoc_ne _ _ _ _ (by simpa [← len] using h)]
        exact off i hia

abbrev Represents {n : ℕ} (C : Circuit) (G : SimpleGraph (Fin n)) (A : Finset (Fin n)) :=
  ∀ x, circuitFun n C x = true ↔ (∃ a ∈ A, x a = true) ∨
    ∃ v w, G.Adj v w ∧ x v = true ∧ x w = true

abbrev Cover {n : ℕ} (G : SimpleGraph (Fin n)) (T : Finset (Fin n)) :=
  ∀ v w, G.Adj v w → v ∈ T ∨ w ∈ T

abbrev BelowEveryCover {n : ℕ} (C : Circuit) (G : SimpleGraph (Fin n)) (A : Finset (Fin n)) :=
  ∀ T : Finset (Fin n), Cover G T → C.size + 1 < A.card + G.edgeSet.ncard + T.card

private theorem positive_of_change {n : ℕ} {C : Circuit} (fan : FanInTwo C) (a : Fin n)
    (out : C.output ≠ a.val) (x y : Fin n → Bool)
    (off : ∀ i, i ≠ a → x i = y i) (diff : circuitFun n C x ≠ circuitFun n C y) :
    1 ≤ readers C.gates a.val := by
  by_contra! zero
  have none : ∀ g ∈ C.gates, a.val ∉ effectiveInputs g := by
    intro g hg h
    have : 0 < readers C.gates a.val :=
      List.length_filter_pos_iff.mpr ⟨g,hg,List.contains_iff_mem.mpr h⟩
    omega
  have equal := agree_except C.gates a.val (fun g hg h hh => by
    have eq : h = g := by simpa using hh
    exact eq.symm ▸ fan g hg) none (List.ofFn x) (List.ofFn y)
    (by simp) (by
      intro i hi
      by_cases hn : i < n
      · simp [List.getD_eq_getElem?_getD, hn, off ⟨i, hn⟩ (fun eq => hi (congrArg Fin.val eq))]
      · simp [List.getD_eq_getElem?_getD, hn]) C.output out
  change circuitFun n C x = circuitFun n C y at equal
  exact diff equal

private theorem singleton_reads {n : ℕ} {C : Circuit} {G : SimpleGraph (Fin n)}
    {A : Finset (Fin n)} (rep : Represents C G A)
    (isolated : ∀ u w, G.Adj u w → u ∉ A) (edge : ∃ u w, G.Adj u w)
    (fan : FanInTwo C) (a : Fin n) (ha : a ∈ A) : 1 ≤ readers C.gates a.val := by
  classical
  obtain ⟨u,w,huw⟩ := edge
  have out : C.output ≠ a.val := by
    intro eq
    let x : Fin n → Bool := fun i => decide (i ∉ A)
    have ht := (rep x).mpr (Or.inr ⟨u,w,huw, by simp [x, isolated u w huw],
      by simp [x, isolated w u huw.symm]⟩)
    simp only [circuitFun, Circuit.eval, wires_eq, eq] at ht
    rw [getD_wiresFrom _ _ _ (by simp)] at ht
    simp [x, ha] at ht
  let x : Fin n → Bool := fun i => decide (i = a)
  let y : Fin n → Bool := fun _ => false
  apply positive_of_change fan a out x y (by intro i hi; simp [x,y,hi])
  intro equal
  have hx := (rep x).mpr (Or.inl ⟨a, ha, by simp [x]⟩)
  have hy := (rep y).mp (equal ▸ hx)
  simp [y] at hy

/-- For every cover T, the ordinary vertices together have strictly fewer
direct gate incidences than the number of edges plus the size of T. -/
theorem below_cover_budget {n : ℕ} {C : Circuit} {G : SimpleGraph (Fin n)}
    {A : Finset (Fin n)} (least : IsMinimalCircuit n C) (rep : Represents C G A)
    (isolated : ∀ u w, G.Adj u w → u ∉ A) (edge : ∃ u w, G.Adj u w)
    (cheap : BelowEveryCover C G A) (T : Finset (Fin n)) (cover : Cover G T) :
    ∑ v ∈ Aᶜ, readers C.gates v.val < G.edgeSet.ncard + T.card := by
  obtain ⟨u,w,huw⟩ := edge
  have yes := (rep (fun _ => true)).mpr (Or.inr ⟨u,w,huw,rfl,rfl⟩)
  have no : circuitFun n C (fun _ => false) ≠ true := by simpa using (rep (fun _ => false)).mp
  have hbudget := input_budget least ⟨_, _, fun eq => no (eq ▸ yes)⟩
  have hA := Finset.sum_le_sum (singleton_reads rep isolated ⟨u,w,huw⟩ least.1)
  simp only [Finset.sum_const, smul_eq_mul, mul_one] at hA
  have hsplit := A.sum_compl_add_sum (fun v => readers C.gates v.val)
  have hcheap := cheap T cover
  omega


private theorem degree_sum {n : ℕ} {G : SimpleGraph (Fin n)} {A : Finset (Fin n)}
    (deg : ∀ v ∉ A, (G.neighborSet v).ncard = 3)
    (isolated : ∀ u w, G.Adj u w → u ∉ A) :
    2 * G.edgeSet.ncard = 3 * Aᶜ.card := by
  classical
  have hA : ∀ v ∈ A, G.degree v = 0 := by
    intro v hv
    apply (G.degree_eq_zero v).mpr
    intro w hw
    exact isolated v w hw hv
  have hOrd : ∀ v ∈ Aᶜ, G.degree v = 3 := by
    intro v hv
    simpa only [SimpleGraph.ncard_neighborSet] using deg v (Finset.mem_compl.mp hv)
  have hs := A.sum_compl_add_sum (fun v => G.degree v)
  rw [Finset.sum_congr rfl hOrd, Finset.sum_congr rfl hA] at hs
  have h := G.sum_degrees_eq_twice_card_edges
  simp only [← SimpleGraph.card_edgeSet, Set.fintypeCard_eq_ncard] at h
  simp at hs
  omega

private theorem small_bipartite_cover {n : ℕ} {G : SimpleGraph (Fin n)}
    {A : Finset (Fin n)} (bip : G.IsBipartite) (isolated : ∀ u w, G.Adj u w → u ∉ A) :
    ∃ T : Finset (Fin n), Cover G T ∧ 2 * T.card ≤ Aᶜ.card := by
  classical
  obtain ⟨s, t, parts⟩ := bip.exists_isBipartiteWith
  let L := Aᶜ.filter (· ∈ s)
  let R := Aᶜ.filter (· ∉ s)
  have sizes : L.card + R.card = Aᶜ.card := Finset.card_filter_add_card_filter_not ..
  have covers : Cover G L ∧ Cover G R := by
    constructor <;> intro v w vw
    all_goals
      have vA := isolated v w vw
      have wA := isolated w v vw.symm
      rcases parts.mem_of_adj vw with ⟨vs, wt⟩ | ⟨vt, ws⟩
      all_goals simp only [L, R, Finset.mem_filter, Finset.mem_compl]
      all_goals grind [Set.disjoint_left.mp parts.disjoint]
  by_cases h : L.card ≤ R.card
  · exact ⟨L, covers.1, by omega⟩
  · exact ⟨R, covers.2, by omega⟩

variable {n : ℕ} {G : SimpleGraph (Fin n)} {A : Finset (Fin n)} {C : Circuit}
    (least : IsMinimalCircuit n C) (rep : Represents C G A)
    (deg : ∀ v ∉ A, (G.neighborSet v).ncard = 3)
    (isolated : ∀ u w, G.Adj u w → u ∉ A) (edge : ∃ u w, G.Adj u w)
    (cheap : BelowEveryCover C G A)

include least rep deg isolated edge cheap

/-- With only the trivial cover of all ordinary vertices, the mean number of
readers is already strictly below five halves. -/
theorem cubic_budget :
    2 * (∑ v ∈ Aᶜ, readers C.gates v.val) < 5 * Aᶜ.card := by
  have h := below_cover_budget least rep isolated edge cheap Aᶜ
    (fun u w e => Or.inl (Finset.mem_compl.mpr (isolated u w e)))
  have he := degree_sum deg isolated
  omega

theorem exists_at_most_two : ∃ v ∉ A, readers C.gates v.val ≤ 2 := by
  by_contra! h
  have bound := Finset.sum_le_sum (s := Aᶜ)
    (fun v hv => show 3 ≤ readers C.gates v.val from h v (Finset.mem_compl.mp hv))
  simp only [Finset.sum_const, smul_eq_mul] at bound
  have hb := cubic_budget least rep deg isolated edge cheap
  omega

/-- Either side of a bipartition covers every edge. The smaller side gives a
strict bound of two readers per ordinary vertex on average. -/
theorem bipartite_budget (bip : G.IsBipartite) :
    (∑ v ∈ Aᶜ, readers C.gates v.val) < 2 * Aᶜ.card := by
  obtain ⟨T, cover, small⟩ := small_bipartite_cover bip isolated
  have h := below_cover_budget least rep isolated edge cheap T cover
  have he := degree_sum deg isolated
  omega

omit edge cheap in
private theorem ordinary_reads (v : Fin n) (hv : v ∉ A) : 1 ≤ readers C.gates v.val := by
  classical
  have nv : (G.neighborSet v).Nonempty := Set.nonempty_of_ncard_ne_zero (by rw [deg v hv]; decide)
  obtain ⟨w, hvw⟩ := nv
  change G.Adj v w at hvw
  have hw := isolated w v hvw.symm
  let single (a : Fin n) : Fin n → Bool := fun i => decide (i = a)
  have off_single (a : Fin n) (ha : a ∉ A) : circuitFun n C (single a) ≠ true := by
    intro h
    rcases (rep _).mp h with ⟨u,hu,ht⟩ | ⟨u,z,uz,ht,hz⟩
    · have : u = a := by simpa [single] using ht
      exact ha (this ▸ hu)
    · have eu : u = a := by simpa [single] using ht
      have ez : z = a := by simpa [single] using hz
      exact uz.ne (eu.trans ez.symm)
  have out : C.output ≠ v.val := by
    intro eq
    apply off_single v hv
    simp only [circuitFun, Circuit.eval, wires_eq, eq]
    rw [getD_wiresFrom _ _ _ (by simp)]
    simp [single]
  let both : Fin n → Bool := fun i => decide (i = v ∨ i = w)
  have yes := (rep both).mpr (Or.inr ⟨v,w,hvw,by simp [both],by simp [both]⟩)
  exact positive_of_change least.1 v out both (single w)
    (by intro i hi; simp [both,single,hi]) (fun eq => off_single w hw (eq ▸ yes))

/-- In the below-cover bipartite case at least one ordinary vertex has exactly
one effective reader, in the actual minimal circuit. -/
theorem exists_one_reader (bip : G.IsBipartite) :
    ∃ v ∉ A, readers C.gates v.val = 1 := by
  by_contra! h
  have atLeastTwo (v : Fin n) (hv : v ∈ Aᶜ) : 2 ≤ readers C.gates v.val := by
    have h1 := ordinary_reads least rep deg isolated v (Finset.mem_compl.mp hv)
    have hne := h v (Finset.mem_compl.mp hv)
    omega
  have bound := Finset.sum_le_sum atLeastTwo
  simp only [Finset.sum_const, smul_eq_mul] at bound
  have hb := bipartite_budget least rep deg isolated edge cheap bip
  omega

/-- Every input read three or more times needs to be offset by a distinct excess
of one-reader inputs in the bipartite below-cover case. -/
theorem more_single_than_heavy (bip : G.IsBipartite) :
    (Aᶜ.filter (fun v => 3 ≤ readers C.gates v.val)).card <
      (Aᶜ.filter (fun v => readers C.gates v.val = 1)).card := by
  let r (v : Fin n) := readers C.gates v.val
  have localCount (v : Fin n) (hv : v ∈ Aᶜ) :
      2 + (if 3 ≤ r v then 1 else 0) ≤ r v + (if r v = 1 then 1 else 0) := by
    have h := ordinary_reads least rep deg isolated v (Finset.mem_compl.mp hv)
    dsimp [r]
    split <;> split <;> omega
  have total := Finset.sum_le_sum localCount
  simp only [Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul, Finset.sum_boole,
    Nat.cast_id] at total
  have h := bipartite_budget least rep deg isolated edge cheap bip
  dsimp [r] at total
  omega

end PEqualNP.Research.ReaderBudget1745
