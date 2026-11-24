import PEqualNP.Research.ReaderBudget1745
import PEqualNP.MetaComplexity.Helpers.L559Up

/-! Local research on the four-gate claim. All theorems here concern the same
graph function as L-meta-1745; no assumption on cycle lengths is needed. -/

namespace PEqualNP.Research.ReaderBudget1745

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.Helpers.L559Up

def SavesFour {n : ℕ} (C : Circuit) (A : Finset (Fin n)) : Prop :=
  ∃ v ∉ A, ∃ s, s + 4 ≤ C.size ∧
    HasCircuitSize n (fun x => circuitFun n C (Function.update x v false)) s

private theorem fromCover (n : ℕ) (G : SimpleGraph (Fin n)) (A T : Finset (Fin n))
    (f : (Fin n → Bool) → Bool) (edge : ∃ u w, G.Adj u w) (cover : Cover G T)
    (sem : ∀ x, f x = true ↔ (∃ a ∈ A, x a = true) ∨
      ∃ u w, G.Adj u w ∧ x u = true ∧ x w = true) :
    ∃ s, s + 1 ≤ A.card + G.edgeSet.ncard + T.card ∧ HasCircuitSize n f s := by
  classical
  obtain ⟨s, hs, hb⟩ := fp_bld_graph n G A T (Or.inr edge) cover
  refine ⟨s, ?_, bld_hasCircuitSize (bld_congr hb ?_)⟩
  · simpa only [← SimpleGraph.card_edgeSet, Set.fintypeCard_eq_ncard] using hs
  · intro x
    cases hf : f x <;> simpa [hf] using (sem x).symm

variable {n : ℕ} {G : SimpleGraph (Fin n)} {A : Finset (Fin n)} {C : Circuit}
    (least : IsMinimalCircuit n C) (rep : Represents C G A)
    (deg : ∀ v ∉ A, (G.neighborSet v).ncard = 3)
    (isolated : ∀ u w, G.Adj u w → u ∉ A) (edge : ∃ u w, G.Adj u w)

include rep deg isolated edge

/-- The cover-construction branch of our original reduction, with the
construction discharged using the project's existing circuit builder. -/
theorem affordable_cover_saves_four (affordable : ¬ BelowEveryCover C G A) : SavesFour C A := by
  classical
  unfold BelowEveryCover at affordable
  push Not at affordable
  obtain ⟨T, hcover, hbudget⟩ := affordable
  obtain ⟨i, j, hij⟩ := edge
  have pick : ∃ v w, v ∈ T ∧ G.Adj v w := by
    rcases hcover i j hij with hi | hj
    · exact ⟨i, j, hi, hij⟩
    · exact ⟨j, i, hj, hij.symm⟩
  obtain ⟨v, w, hvT, hvw⟩ := pick
  have hvA := isolated v w hvw
  have hwA := isolated w v hvw.symm
  have alive : ∃ z, G.Adj w z ∧ z ≠ v := by
    by_contra! h
    have sub : G.neighborSet w ⊆ {v} := fun z hz => h z hz
    have := Set.ncard_le_ncard sub
    simp [deg w hwA] at this
  obtain ⟨z, hwz, hz⟩ := alive
  have edge' : (G.deleteIncidenceSet v).Adj w z :=
    SimpleGraph.deleteIncidenceSet_adj.mpr ⟨hwz, hvw.ne.symm, hz⟩
  have cover' : ∀ i j, (G.deleteIncidenceSet v).Adj i j → i ∈ T.erase v ∨ j ∈ T.erase v := by
    intro i j h
    obtain ⟨hij, hi, hj⟩ := SimpleGraph.deleteIncidenceSet_adj.mp h
    simpa [Finset.mem_erase, hi, hj] using hcover i j hij
  have sem' : ∀ x : Fin n → Bool, circuitFun n C (Function.update x v false) = true ↔
      (∃ a ∈ A, x a = true) ∨
        ∃ i j, (G.deleteIncidenceSet v).Adj i j ∧ x i = true ∧ x j = true := by
    intro x
    rw [rep]
    have upd (i : Fin n) : Function.update x v false i = true ↔ i ≠ v ∧ x i = true := by
      by_cases h : i = v <;> simp [h]
    simp only [upd, SimpleGraph.deleteIncidenceSet_adj]
    grind
  obtain ⟨s, hs, hsize⟩ := fromCover n (G.deleteIncidenceSet v) A (T.erase v) _
    ⟨w, z, edge'⟩ cover' sem'
  refine ⟨v, hvA, s, ?_, hsize⟩
  have removed := G.card_edgeFinset_deleteIncidenceSet v
  have enough := G.degree_le_card_edgeFinset v
  simp only [← SimpleGraph.card_edgeSet, Set.fintypeCard_eq_ncard,
    ← SimpleGraph.ncard_neighborSet] at removed enough
  rw [deg v hvA] at removed enough
  rw [removed, Finset.card_erase_of_mem hvT] at hs
  have pos := Finset.card_pos.mpr ⟨v, hvT⟩
  omega

include least

/-- A certificate using only the circuit's direct input reads and a graph cover. -/
theorem enough_reads_save_four (T : Finset (Fin n)) (cover : Cover G T)
    (enough : G.edgeSet.ncard + T.card ≤ ∑ v ∈ Aᶜ, readers C.gates v.val) :
    SavesFour C A := by
  apply affordable_cover_saves_four rep deg isolated edge
  intro cheap
  exact (not_lt_of_ge enough) (below_cover_budget least rep isolated edge cheap T cover)

/-- In particular, the all-three-reader case of the earlier fanout split closes. -/
theorem all_three_save_four (three : ∀ v ∉ A, 3 ≤ readers C.gates v.val) : SavesFour C A := by
  apply affordable_cover_saves_four rep deg isolated edge
  intro cheap
  obtain ⟨v,hv,low⟩ := exists_at_most_two least rep deg isolated edge cheap
  have := three v hv
  omega

/-- On bipartite graphs, this includes mixtures of one-, two-, and
three-reader vertices. Only a strict surplus of one-reader vertices remains. -/
theorem bipartite_save_four (bip : G.IsBipartite)
    (balance : (Aᶜ.filter (fun v => readers C.gates v.val = 1)).card ≤
      (Aᶜ.filter (fun v => 3 ≤ readers C.gates v.val)).card) :
    SavesFour C A := by
  apply affordable_cover_saves_four rep deg isolated edge
  intro cheap
  exact (not_lt_of_ge balance) (more_single_than_heavy least rep deg isolated edge cheap bip)

end PEqualNP.Research.ReaderBudget1745
