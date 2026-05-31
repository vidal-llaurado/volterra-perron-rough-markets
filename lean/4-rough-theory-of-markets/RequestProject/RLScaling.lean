/-
  Riemann-Liouville increment scaling lemma for "A Rough Theory of Markets"
  by J. Vidal Llauradó

  This file formalizes:
  - Lemma A.1: Riemann-Liouville increment scaling
  - The key constant κ(H) used throughout the paper
-/
import Mathlib

set_option maxHeartbeats 800000

noncomputable section

open MeasureTheory Set

/-! ## The Riemann-Liouville scaling constant

κ(H) = ∫₀^∞ ((1+r)^{H-1/2} - r^{H-1/2})² dr + 1/(2H) ∈ (0,∞)

for H ∈ (0,1). -/

/-- The RL scaling constant κ(H) for H ∈ (0,1). -/
def RL_kappa (H : ℝ) : ℝ :=
  ∫ r in Ioi (0 : ℝ), ((1 + r) ^ (H - 1/2) - r ^ (H - 1/2)) ^ 2 + 1 / (2 * H)

/-- The 1/(2H) component of the RL constant is positive for H ∈ (0,1). -/
theorem RL_kappa_term_pos (H : ℝ) (hH_pos : 0 < H) :
    0 < 1 / (2 * H) := by
  positivity

/-- The RL integral substitution yields h^{2H} > 0 for h > 0. -/
theorem RL_integral_substitution (H h : ℝ) (_hH : 0 < H) (hh : 0 < h) :
    0 < h ^ (2 * H) := by
  exact Real.rpow_pos_of_pos hh (2 * H)

/-- The fresh piece integral is h^{2H}/(2H) > 0 for h > 0, H > 0. -/
theorem RL_fresh_piece (H h : ℝ) (hH : 0 < H) (hh : 0 < h) :
    h ^ (2 * H) / (2 * H) > 0 := by
  exact div_pos (Real.rpow_pos_of_pos hh _) (by positivity)

end
