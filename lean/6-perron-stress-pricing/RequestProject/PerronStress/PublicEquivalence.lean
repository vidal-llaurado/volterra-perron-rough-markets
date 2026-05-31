/-
# Perron Stress Pricing: Public Equivalence

Formalization of Proposition 2.4, Lemma 3.2, and related results from:
  "Perron Stress Pricing under Public Compression"
  by J. Vidal Llauradó (2026)
-/
import Mathlib
import RequestProject.PerronStress.Defs

open MeasureTheory MeasurableSpace Filter
open scoped ENNReal NNReal BigOperators

noncomputable section

variable {Ω : Type*} {m₀ : MeasurableSpace Ω} {μ : Measure Ω}
variable [IsFiniteMeasure μ]

namespace PerronStress

/-! ## Proposition 2.4: Exact public-equivalence condition -/

/-
Proposition 2.4 (forward direction): If `E_Q[Z | H] = 1` a.e.,
then `E_Q[Z · Y] = E_Q[Y]` for every H-measurable integrable `Y`.
-/
theorem public_equivalence_forward
    (S : Setup Ω m₀ μ)
    (Z : Ω → ℝ)
    (hZ_condexp : μ[Z | S.mH] =ᵐ[μ] fun _ => (1 : ℝ))
    (Y : Ω → ℝ)
    (hY_meas : @StronglyMeasurable Ω ℝ _ S.mH Y)
    (hY_int : Integrable Y μ)
    (hZY_int : Integrable (fun ω => Z ω * Y ω) μ) :
    ∫ ω, Z ω * Y ω ∂μ = ∫ ω, Y ω ∂μ := by
  have h_integral : ∫ ω, Z ω * Y ω ∂μ = ∫ ω, μ[Z * Y | S.mH] ω ∂μ := by
    rw [ MeasureTheory.integral_condExp ];
    · rfl;
    · exact le_trans S.hHG ( le_trans S.hGK S.hK0 );
  have h_condexp : μ[Z * Y | S.mH] =ᵐ[μ] fun ω => Y ω := by
    have h_cond_exp : μ[Z * Y | S.mH] =ᵐ[μ] μ[Z | S.mH] * Y := by
      apply_rules [ MeasureTheory.condExp_mul_of_stronglyMeasurable_right ];
      have := @MeasureTheory.condExp_congr_ae;
      contrapose! this;
      use Ω, ℝ, S.mH, m₀, μ, Z, 0;
      simp_all +decide [ MeasureTheory.condExp ];
      rw [ Filter.EventuallyEq, MeasureTheory.ae_iff ] at hZ_condexp ; aesop;
    filter_upwards [ h_cond_exp, hZ_condexp ] with ω hω₁ hω₂ using by simpa [ hω₂ ] using hω₁;
  rw [ h_integral, MeasureTheory.integral_congr_ae h_condexp ]

/-
Helper lemma: For H-measurable set A, the indicator function is H-strongly-measurable.
-/
private theorem indicator_stronglyMeasurable_of_sub
    (S : Setup Ω m₀ μ)
    (A : Set Ω) (hA : @MeasurableSet Ω S.mH A) :
    @StronglyMeasurable Ω ℝ _ S.mH (Set.indicator A (fun _ => (1 : ℝ))) := by
  apply_rules [ Measurable.stronglyMeasurable ];
  exact Measurable.ite hA measurable_const measurable_const

/-
Helper lemma: set integral identity from the global integral hypothesis.
    If ∫ Z·Y = ∫ Y for all H-strongly-measurable integrable Y,
    then ∫_A Z = μ(A) for all H-measurable finite-measure sets A.
-/
private theorem setIntegral_eq_of_forall_integral
    (S : Setup Ω m₀ μ)
    (Z : Ω → ℝ)
    (hZ_int : Integrable Z μ)
    (hZY : ∀ (Y : Ω → ℝ),
      @StronglyMeasurable Ω ℝ _ S.mH Y → Integrable Y μ →
      Integrable (fun ω => Z ω * Y ω) μ →
      ∫ ω, Z ω * Y ω ∂μ = ∫ ω, Y ω ∂μ)
    (A : Set Ω) (hA : @MeasurableSet Ω S.mH A) (hA_fin : μ A < ⊤) :
    ∫ ω in A, Z ω ∂μ = (μ A).toReal := by
  convert hZY _ ?_ ?_ ?_ using 1;
  rw [ ← MeasureTheory.integral_indicator ];
  any_goals exact Set.indicator A 1;
  all_goals norm_num [ Set.indicator ];
  · exact S.hHG.trans ( S.hGK.trans S.hK0 ) A hA;
  · erw [ MeasureTheory.integral_indicator ( S.hHG.trans ( S.hGK.trans S.hK0 ) A hA ) ] ; aesop;
  · exact Measurable.stronglyMeasurable ( measurable_const.indicator hA );
  · exact MeasureTheory.integrable_indicator_iff ( S.hHG.trans ( S.hGK.trans S.hK0 ) A hA ) |>.2 ( MeasureTheory.integrable_const _ );
  · refine' hZ_int.indicator _;
    exact S.hHG.trans ( S.hGK.trans S.hK0 ) A hA

/-
Proposition 2.4 (backward direction): If `E_Q[Z · Y] = E_Q[Y]`
for every bounded H-measurable `Y`, then `E_Q[Z | H] = 1` a.e.
-/
theorem public_equivalence_backward
    (S : Setup Ω m₀ μ)
    (Z : Ω → ℝ)
    (hZ_int : Integrable Z μ)
    (hZY : ∀ (Y : Ω → ℝ),
      @StronglyMeasurable Ω ℝ _ S.mH Y → Integrable Y μ →
      Integrable (fun ω => Z ω * Y ω) μ →
      ∫ ω, Z ω * Y ω ∂μ = ∫ ω, Y ω ∂μ) :
    μ[Z | S.mH] =ᵐ[μ] fun _ => (1 : ℝ) := by
  convert ( ae_eq_condExp_of_forall_setIntegral_eq ( le_trans S.hHG ( le_trans S.hGK S.hK0 ) ) _ _ _ _ ) |>.symm using 1;
  · exact S.hSigmaFiniteH;
  · exact hZ_int;
  · exact fun s _ _ => MeasureTheory.integrable_const _;
  · intro s hs hμs
    have h_integral_eq : ∫ ω in s, Z ω ∂μ = (μ s).toReal := by
      exact?;
    aesop;
  · exact MeasureTheory.aestronglyMeasurable_const

/-! ## Dynamic-safe implies public-equivalent (tower property) -/

/-- Part of Definition 3.1: Every dynamic-safe density is also public-equivalent.
    If `E_Q[Z | G] = 1` and `H ≤ G`, then `E_Q[Z | H] = 1`. -/
theorem dynamicSafe_implies_publicEquiv
    (S : Setup Ω m₀ μ)
    (Z : Ω → ℝ)
    (hZ : IsDynamicSafeDensity S Z) :
    μ[Z | S.mH] =ᵐ[μ] fun _ => (1 : ℝ) := by
  obtain ⟨ hZ_pos, hZ_int, hZ_eq ⟩ := hZ;
  have h_cond_exp : μ[μ[Z | S.mG] | S.mH] =ᵐ[μ] μ[Z | S.mH] := by
    apply_rules [ MeasureTheory.condExp_condExp_of_le ]
    · exact S.hHG
    · exact le_trans S.hGK S.hK0
  refine' h_cond_exp.symm.trans _
  convert MeasureTheory.condExp_congr_ae hZ_eq using 1
  rw [ MeasureTheory.condExp_const ]
  exact le_trans S.hHG ( le_trans S.hGK S.hK0 )

/-! ## Lemma 3.2: Public prices are preserved -/

/-- Lemma 3.2: If `Q'` is public-equivalent to `Q`,
then `E_{Q'}[Y] = E_Q[Y]` for every bounded H-measurable `Y`. -/
theorem public_prices_preserved
    (S : Setup Ω m₀ μ)
    (Z : Ω → ℝ)
    (hZ : IsPublicEquivDensity S Z)
    (Y : Ω → ℝ)
    (hY_meas : @StronglyMeasurable Ω ℝ _ S.mH Y)
    (hY_int : Integrable Y μ)
    (hZY_int : Integrable (fun ω => Z ω * Y ω) μ) :
    ∫ ω, Z ω * Y ω ∂μ = ∫ ω, Y ω ∂μ := by
  exact public_equivalence_forward S Z hZ.2.2 Y hY_meas hY_int hZY_int

end PerronStress

end