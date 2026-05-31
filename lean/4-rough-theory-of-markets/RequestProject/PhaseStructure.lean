/-
  Phase structure theorem for "A Rough Theory of Markets"
  by J. Vidal Llauradó

  This file formalizes:
  - Theorem 7.8: Phase structure of admissible contagion regimes
  - Definition 7.7: Contagion phases at market scale
-/
import RequestProject.Defs
import RequestProject.Admissibility

set_option maxHeartbeats 800000

open Finset BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

namespace VolterraMarket

variable {N : ℕ} (m : VolterraMarket N)

/-! ## Theorem 7.8: Phase structure of admissible contagion regimes -/

/-- Phase (i): All active off-diagonal edges smooth implies smooth-degenerate phase.
    In this phase, no active off-diagonal channel generates a nondegenerate
    shrinking projected experiment. -/
theorem smooth_degenerate_phase
    (h_all_smooth : ∀ (i j : Fin N), i ≠ j → m.w i * m.β i j ≠ 0 → 1/2 ≤ m.H i j) :
    m.admissibleEdges = ∅ := by
  rw [Finset.eq_empty_iff_forall_notMem]
  intro ⟨i, j⟩ hmem
  rw [mem_admissibleEdges] at hmem
  exact absurd hmem.2.2 (not_lt.mpr (h_all_smooth i j hmem.1 hmem.2.1))

/-- Phase (ii): Under admissible dominant asymmetry, H_M < 1/2. -/
theorem rough_observable_phase
    (hne : m.hasActiveEdges) (hnc : m.noncancelling hne)
    (hada : m.AdmissibleDominantAsymmetry hne) :
    m.H_M hne hnc < 1/2 :=
  m.market_roughness_necessity hne hnc hada

/-- Phase classification: either all edges smooth, or admissible class nonempty. -/
theorem phase_classification
    (_has_offdiag : ∃ i j : Fin N, i ≠ j ∧ m.w i * m.β i j ≠ 0) :
    (∀ (i j : Fin N), i ≠ j → m.w i * m.β i j ≠ 0 → 1/2 ≤ m.H i j) ∨
    m.admissibleEdges.Nonempty := by
  by_cases h : ∀ (i j : Fin N), i ≠ j → m.w i * m.β i j ≠ 0 → 1/2 ≤ m.H i j
  · left; exact h
  · right
    push_neg at h
    obtain ⟨i, j, hij, hactive, hrough⟩ := h
    exact m.admissibility_nonvacuous i j hij hactive hrough

/-- In the smooth-degenerate phase, no admissible off-diagonal channel survives. -/
theorem smooth_phase_no_admissible
    (h_smooth : ∀ (i j : Fin N), i ≠ j → m.w i * m.β i j ≠ 0 → 1/2 ≤ m.H i j)
    (i j : Fin N) (hij : i ≠ j) (hactive : m.w i * m.β i j ≠ 0) :
    ¬ m.isAdmissible i j :=
  m.smooth_failure i j (h_smooth i j hij hactive)

end VolterraMarket
end
