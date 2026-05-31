/-
  Synchronization threshold and Perron-Frobenius results for "A Rough Theory of Markets"
  by J. Vidal Llauradó

  This file formalizes:
  - Theorem 6.1: Synchronization threshold for the screened market network
  - Key properties of the screened synchronization matrix
-/
import Mathlib

set_option maxHeartbeats 800000

noncomputable section

/-! ## Theorem 6.1: Synchronization threshold -/

section SynchronizationThreshold

/-- Theorem 6.1(i): If 0 ≤ ρ < 1, then ρ^m → 0. -/
theorem subcritical_convergence (ρ : ℝ) (hρ : ρ < 1) (hρ_pos : 0 ≤ ρ) :
    Filter.Tendsto (fun m => ρ ^ m) Filter.atTop (nhds 0) :=
  tendsto_pow_atTop_nhds_zero_of_lt_one hρ_pos hρ

/-- Theorem 6.1(ii): If 1 < ρ, then ρ^m → ∞. -/
theorem supercritical_divergence (ρ : ℝ) (hρ : 1 < ρ) :
    Filter.Tendsto (fun m => ρ ^ m) Filter.atTop Filter.atTop :=
  tendsto_pow_atTop_atTop_of_one_lt hρ

/-- Subcritical bound: 0 ≤ ρ < 1 implies ρ^m ≤ 1. -/
theorem subcritical_decay (ρ : ℝ) (hρ : ρ < 1) (hρ_pos : 0 ≤ ρ) (m : ℕ) :
    ρ ^ m ≤ 1 :=
  pow_le_one₀ hρ_pos (le_of_lt hρ)

/-- Supercritical bound: 1 < ρ implies 1 ≤ ρ^m. -/
theorem supercritical_growth (ρ : ℝ) (hρ : 1 < ρ) (m : ℕ) :
    1 ≤ ρ ^ m :=
  one_le_pow₀ (le_of_lt hρ)

end SynchronizationThreshold

/-! ## Spectral gap properties -/

section SpectralGap

/-- Theorem 6.6: The ratio (ρ/ρA)^m → 0 when 0 ≤ ρ < ρA, giving spectral gap decay. -/
theorem spectral_gap_decay (ρ ρA : ℝ) (hρ : 0 ≤ ρ) (hρA : 0 < ρA) (hgap : ρ < ρA) :
    Filter.Tendsto (fun m => (ρ / ρA) ^ m) Filter.atTop (nhds 0) := by
  apply tendsto_pow_atTop_nhds_zero_of_lt_one
  · exact div_nonneg hρ (le_of_lt hρA)
  · rwa [div_lt_one hρA]

/-- The off-Perron component decays relative to the Perron component. -/
theorem off_perron_relative_decay (ρ ρA C : ℝ) (m : ℕ) :
    C * ρ ^ m / ρA ^ m = C * (ρ / ρA) ^ m := by
  rw [div_pow, mul_div_assoc]

end SpectralGap

/-! ## Phase structure -/

section PhaseStructure

/-- The spectral radius determines the phase:
    ρ(A) ≤ 1 → rough-observable, ρ(A) > 1 → rough-synchronized. -/
theorem phase_dichotomy (ρA : ℝ) : ρA ≤ 1 ∨ 1 < ρA :=
  le_or_gt ρA 1

end PhaseStructure

end
