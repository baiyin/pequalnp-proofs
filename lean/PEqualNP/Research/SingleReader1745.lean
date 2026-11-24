import PEqualNP.Research.CoverSavings1745

/-! A solitary reader cannot combine two distinct ordinary input variables by
AND or OR. The proof distinguishes the graph function on a pair of assignments
where that gate is forced to a constant. -/

namespace PEqualNP.Research.ReaderBudget1745

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.Helpers

private def absorbOp : Bool → GateOp
  | false => .and
  | true => .or

private theorem absorbs (b : Bool) (g : Gate) (f : ℕ → Bool) (w : ℕ)
    (op : g.op = absorbOp b) (mem : w ∈ g.inputs) (fixed : f w = b) :
    g.op.eval (g.inputs.map f) = b := by
  cases b
  · simp only [op, absorbOp, GateOp.eval, List.all_eq_false, List.mem_map]
    exact ⟨false, ⟨w, mem, fixed⟩, by decide⟩
  · simp only [op, absorbOp, GateOp.eval, List.any_eq_true, List.mem_map]
    exact ⟨true, ⟨w, mem, fixed⟩, rfl⟩

private theorem masked_wires (gs : List Gate) (v w : ℕ) (b : Bool)
    (fan : ∀ g ∈ gs, FanInTwo ⟨[g], 0⟩)
    (mask : ∀ g ∈ gs, v ∈ effectiveInputs g → g.op = absorbOp b ∧ w ∈ g.inputs)
    (x y : List Bool) (hw : w < x.length) (len : x.length = y.length)
    (fx : x.getD w false = b) (fy : y.getD w false = b)
    (off : ∀ i, i ≠ v → x.getD i false = y.getD i false) :
    ∀ i, i ≠ v → (wiresFrom gs x).getD i false = (wiresFrom gs y).getD i false := by
  induction gs generalizing x y with
  | nil => exact off
  | cons g gs ih =>
    have eqGate : g.op.eval (g.inputs.map (fun i => x.getD i false)) =
        g.op.eval (g.inputs.map (fun i => y.getD i false)) := by
      by_cases hit : v ∈ effectiveInputs g
      · obtain ⟨op,mem⟩ := mask g (by simp) hit
        exact (absorbs b g _ w op mem fx).trans (absorbs b g _ w op mem fy).symm
      · rw [effective_eval g (fan g (by simp)), effective_eval g (fan g (by simp))]
        congr 1
        exact List.map_congr_left fun i hi => off i (fun eq => hit (eq ▸ hi))
    simp only [wiresFrom, List.foldl_cons] at ih ⊢
    rw [eqGate]
    apply ih (fun a ha => fan a (by simp [ha])) (fun a ha => mask a (by simp [ha]))
    · simp; omega
    · simp [len]
    · rwa [List.getD_append _ _ _ _ hw]
    · rwa [List.getD_append _ _ _ _ (len ▸ hw)]
    · intro i hi
      by_cases h : i = x.length
      · subst i; simp [len]
      · rw [getD_snoc_ne _ _ _ _ h, getD_snoc_ne _ _ _ _ (by simpa [← len] using h)]
        exact off i hi

private theorem escape_square {n : ℕ} {G : SimpleGraph (Fin n)} {v w : Fin n}
    (distinct : v ≠ w) (deg : (G.neighborSet v).ncard = 3)
    (girth : ∀ a (p : G.Walk a a), p.IsCycle → 7 ≤ p.length) :
    ∃ z, G.Adj v z ∧ ¬ G.Adj w z := by
  by_contra! h
  obtain ⟨s,t,hs,ht,hst⟩ := (Set.one_lt_ncard_iff (G.neighborSet v).toFinite).mp (show 1 < (G.neighborSet v).ncard by omega)
  change G.Adj v s at hs
  change G.Adj v t at ht
  have ws := h s hs
  have wt := h t ht
  let p : G.Walk v v := .cons hs (.cons ws.symm (.cons wt (.cons ht.symm .nil)))
  have cycle : p.IsCycle := by
    rw [SimpleGraph.Walk.isCycle_iff_isPath_tail_and_le_length]
    constructor
    · simp [p, SimpleGraph.Walk.cons_isPath_iff, distinct.symm,
        hs.ne.symm, ht.ne.symm, ws.ne.symm, wt.ne, hst]
    · simp [p]
  have bad := girth v p cycle
  simp [p] at bad

private theorem test_pair {n : ℕ} {G : SimpleGraph (Fin n)} {A : Finset (Fin n)}
    {v w : Fin n} (distinct : v ≠ w) (wA : w ∉ A)
    (deg : (G.neighborSet v).ncard = 3) (isolated : ∀ i j, G.Adj i j → i ∉ A)
    (girth : ∀ a (p : G.Walk a a), p.IsCycle → 7 ≤ p.length)
    {C : Circuit} (rep : Represents C G A) (b : Bool) :
    ∃ x y : Fin n → Bool, x w = b ∧ y w = b ∧ (∀ i, i ≠ v → x i = y i) ∧
      circuitFun n C x = true ∧ circuitFun n C y ≠ true := by
  classical
  obtain ⟨z, vz, extra⟩ : ∃ z, G.Adj v z ∧
      (if b then ¬ G.Adj w z else z ≠ w) := by
    cases b with
    | false => simpa using Set.exists_ne_of_one_lt_ncard (show 1 < (G.neighborSet v).ncard by omega) w
    | true => simpa using escape_square distinct deg girth
  have zA := isolated z v vz.symm
  let y : Fin n → Bool := fun i => decide (i = z ∨ (b = true ∧ i = w))
  let x : Fin n → Bool := fun i => decide (i = v) || y i
  refine ⟨x,y,?_,?_,?_,?_,?_⟩
  · cases b <;> simp_all [x,y,Ne.symm]
  · cases b <;> simp_all [y,Ne.symm]
  · intro i hi; simp [x,hi]
  · apply (rep x).mpr
    exact Or.inr ⟨v,z,vz,by simp [x],by simp [x,y]⟩
  · intro h
    have hbad := (rep y).mp h
    simp only [y, decide_eq_true_eq] at hbad
    rcases hbad with ⟨a,ha,hh⟩ | ⟨i,j,ij,hi,hj⟩
    · grind
    · have neq := ij.ne
      have symm := ij.symm
      cases b <;> simp_all
      grind

/-- If exactly one gate effectively reads v, its AND or OR partner cannot be a
distinct ordinary primary input. An internal wire or NOT remains possible. -/
theorem single_reader_excludes_primary_pair {n : ℕ} {G : SimpleGraph (Fin n)} {A : Finset (Fin n)}
    {C : Circuit} (fan : FanInTwo C) (rep : Represents C G A)
    (isolated : ∀ i j, G.Adj i j → i ∉ A)
    (girth : ∀ a (p : G.Walk a a), p.IsCycle → 7 ≤ p.length)
    (v w : Fin n) (distinct : v ≠ w) (vA : v ∉ A) (wA : w ∉ A)
    (deg : (G.neighborSet v).ncard = 3) (g : Gate)
    (sole : C.gates.filter (fun h => (effectiveInputs h).contains v.val) = [g])
    (partner : w.val ∈ g.inputs) : g.op ≠ .and ∧ g.op ≠ .or := by
  have out : C.output ≠ v.val := by
    intro eq
    let y : Fin n → Bool := fun i => decide (i = v)
    have on : circuitFun n C y = true := by
      simp only [circuitFun, Circuit.eval, wires_eq, eq]
      rw [getD_wiresFrom _ _ _ (by simp)]
      simp [y]
    have off := (rep y).mp on
    simp [y] at off
    exact vA off
  have impossible (b : Bool) (op : g.op = absorbOp b) : False := by
    obtain ⟨x,y,hx,hy,off,yes,no⟩ := test_pair distinct wA deg isolated girth rep b
    have hmask (h : Gate) (hh : h ∈ C.gates) (reads : v.val ∈ effectiveInputs h) :
        h.op = absorbOp b ∧ w.val ∈ h.inputs := by
      have hh' : h ∈ C.gates.filter (fun k => (effectiveInputs k).contains v.val) :=
        List.mem_filter.mpr ⟨hh,List.contains_iff_mem.mpr reads⟩
      rw [sole, List.mem_singleton] at hh'
      exact hh' ▸ ⟨op,partner⟩
    have eq := masked_wires C.gates v.val w.val b
      (fun h hh k hk => by
        have e : k = h := by simpa using hk
        exact e.symm ▸ fan h hh) hmask (List.ofFn x) (List.ofFn y)
      (by simp) (by simp) (by simpa using hx) (by simpa using hy)
      (by
        intro i hi
        by_cases bound : i < n
        · simp [List.getD_eq_getElem?_getD, bound,
            off ⟨i,bound⟩ (fun e => hi (congrArg Fin.val e))]
        · simp [List.getD_eq_getElem?_getD,bound]) C.output out
    change circuitFun n C x = circuitFun n C y at eq
    exact no (eq ▸ yes)
  exact ⟨impossible false, impossible true⟩

/-- Any bipartite counterexample must have the stated imbalance and a witness
with a unique reader. Every such reader is subject to the gate restriction. -/
theorem bipartite_counterexample_shape {n : ℕ} {G : SimpleGraph (Fin n)} {A : Finset (Fin n)}
    {C : Circuit} (least : IsMinimalCircuit n C) (rep : Represents C G A)
    (deg : ∀ v ∉ A, (G.neighborSet v).ncard = 3)
    (isolated : ∀ i j, G.Adj i j → i ∉ A) (edge : ∃ u w, G.Adj u w)
    (girth : ∀ a (p : G.Walk a a), p.IsCycle → 7 ≤ p.length)
    (bip : G.IsBipartite) (wouldFail : ¬ SavesFour C A) :
    (Aᶜ.filter (fun v => 3 ≤ readers C.gates v.val)).card <
      (Aᶜ.filter (fun v => readers C.gates v.val = 1)).card ∧
    ∃ v ∉ A, ∃ g : Gate,
      C.gates.filter (fun h => (effectiveInputs h).contains v.val) = [g] ∧
      ∀ w ∉ A, v ≠ w → w.val ∈ g.inputs → g.op ≠ .and ∧ g.op ≠ .or := by
  classical
  have cheap : BelowEveryCover C G A := by
    by_contra affordable
    exact wouldFail (affordable_cover_saves_four rep deg isolated edge affordable)
  refine ⟨more_single_than_heavy least rep deg isolated edge cheap bip, ?_⟩
  obtain ⟨v, hv, one⟩ := exists_one_reader least rep deg isolated edge cheap bip
  obtain ⟨g, sole⟩ := List.length_eq_one_iff.mp one
  exact ⟨v, hv, g, sole, fun w hw diff mem =>
    single_reader_excludes_primary_pair least.1 rep isolated girth v w diff hv hw (deg v hv) g sole mem⟩

end PEqualNP.Research.ReaderBudget1745
