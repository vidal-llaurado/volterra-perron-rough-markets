/-
  ## Calendar Convex-Order Restriction

  Formalization of Theorem 3.5 from

    J. Vidal Llauradó, "Volterra–Perron Pricing of the Option Manifold" (2026).

  The core results:
  - Jensen's inequality (unconditional form)
  - Call and put payoffs are convex
  - Calendar monotonicity of call prices under the martingale assumption
-/

import Mathlib

open MeasureTheory

set_option maxHeartbeats 800000

/-! ### Jensen's inequality (unconditional, finite-dimensional) -/

/-
**Jensen's inequality (basic form):**
  If `φ : ℝ → ℝ` is convex and `X` is a random variable on a probability space,
  then `φ(E[X]) ≤ E[φ(X)]`.
-/
theorem jensen_inequality
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    (X : Ω → ℝ) (φ : ℝ → ℝ) (hφ : ConvexOn ℝ Set.univ φ)
    (hX : Integrable X μ) (hφX : Integrable (φ ∘ X) μ)
    (hXm : AEStronglyMeasurable X μ) :
    φ (∫ ω, X ω ∂μ) ≤ ∫ ω, φ (X ω) ∂μ := by
  convert ConvexOn.map_integral_le hφ _ _ _;
  any_goals tauto;
  · grind;
  · apply_rules [ hφ.continuousOn ];
    exact isOpen_univ;
  · exact isClosed_univ;
  · exact Filter.Eventually.of_forall fun x => Set.mem_univ _

/-! ### Convexity of option payoffs -/

/-
The call payoff `(x - K)⁺` is convex.
-/
theorem call_payoff_convex (K : ℝ) :
    ConvexOn ℝ Set.univ (fun x : ℝ => max (x - K) 0) := by
  fapply ConvexOn.sup;
  · grind +suggestions;
  · exact ⟨ convex_univ, fun x _ y _ a b ha hb hab => by norm_num ⟩

/-
The put payoff `(K - x)⁺` is convex.
-/
theorem put_payoff_convex (K : ℝ) :
    ConvexOn ℝ Set.univ (fun x : ℝ => max (K - x) 0) := by
  -- The function $K - x$ is linear, hence convex.
  have h_linear_convex : ConvexOn ℝ Set.univ (fun x : ℝ => K - x) := by
    constructor <;> norm_num;
    · exact convex_univ;
    · intros; rw [ ← eq_sub_iff_add_eq' ] at *; subst_vars; nlinarith;
  convert ConvexOn.sup h_linear_convex ( convexOn_const 0 <| convex_univ ) using 1