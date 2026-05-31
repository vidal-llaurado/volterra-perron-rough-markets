/-
# Perron Stress Pricing: Nested Residuals (Pythagorean Identity)

Formalization of Theorem 2.7 (nested surface and public-terminal residuals)
and the Three-Part Hedge Decomposition (Theorem 5.3) from:
  "Perron Stress Pricing under Public Compression"
  by J. Vidal Llauradó (2026)
-/
import Mathlib
import RequestProject.PerronStress.Defs

open MeasureTheory MeasurableSpace Filter
open scoped ENNReal NNReal BigOperators

noncomputable section

variable {Ω : Type*} {m₀ : MeasurableSpace Ω} {μ : Measure Ω}
variable [IsProbabilityMeasure μ]

namespace PerronStress

/-! ## Theorem 2.7: Nested surface and public-terminal residuals

For `H ⊆ G ⊆ K` and `L = E[X | K]`:
  ‖L - E[L|H]‖² = ‖L - E[L|G]‖² + ‖E[L|G] - E[L|H]‖²

This is the Pythagorean identity for nested orthogonal projections.
-/

/-
Theorem 2.7 (orthogonal decomposition):
The residual `L - E[L|H]` decomposes orthogonally as
`(L - E[L|G]) + (E[L|G] - E[L|H])`.

We formalize this as: the inner product between the two components is zero.
The inner product ⟨f, g⟩ = ∫ f · g dμ.
-/
theorem nested_residuals_orthogonal
    (S : Setup Ω m₀ μ)
    (L : Ω → ℝ)
    (hL_Kmeas : @StronglyMeasurable Ω ℝ _ S.mK L)
    (hL_int : MeasureTheory.Integrable L μ)
    (hL_sq : MeasureTheory.Integrable (fun ω => L ω ^ 2) μ)
    (hcondG_int : MeasureTheory.Integrable (fun ω => μ[L | S.mG] ω) μ)
    (hcondH_int : MeasureTheory.Integrable (fun ω => μ[L | S.mH] ω) μ)
    (hprod_int : MeasureTheory.Integrable
      (fun ω => (L ω - μ[L | S.mG] ω) * (μ[L | S.mG] ω - μ[L | S.mH] ω)) μ) :
    ∫ ω, (L ω - μ[L | S.mG] ω) * (μ[L | S.mG] ω - μ[L | S.mH] ω) ∂μ = 0 := by
  -- By Fubini's theorem, we can interchange the order of integration.
  have h_fubini : ∫ ω, (L ω - μ[L | S.mG] ω) * (μ[L | S.mG] ω - μ[L | S.mH] ω) ∂μ = ∫ ω, (μ[L | S.mG] ω - μ[L | S.mH] ω) * (L ω - μ[L | S.mG] ω) ∂μ := by
    ac_rfl;
  have h_fubini : ∫ ω, (μ[L | S.mG] ω - μ[L | S.mH] ω) * (L ω - μ[L | S.mG] ω) ∂μ = ∫ ω, (μ[L | S.mG] ω - μ[L | S.mH] ω) * (μ[L - μ[L | S.mG] | S.mG] ω) ∂μ := by
    have h_fubini : ∫ ω, (μ[L | S.mG] ω - μ[L | S.mH] ω) * (L ω - μ[L | S.mG] ω) ∂μ = ∫ ω, (μ[L | S.mG] ω - μ[L | S.mH] ω) * (μ[L - μ[L | S.mG] | S.mG] ω) ∂μ := by
      have h_fubini : ∫ ω, (μ[L | S.mG] ω - μ[L | S.mH] ω) * (L ω - μ[L | S.mG] ω) ∂μ = ∫ ω, (L ω - μ[L | S.mG] ω) * (μ[L | S.mG] ω - μ[L | S.mH] ω) ∂μ := by
        grind
      rw [ h_fubini, ← integral_condExp ( show S.mG ≤ m₀ from S.hGK.trans S.hK0 ) ];
      rw [ MeasureTheory.integral_congr_ae ];
      convert MeasureTheory.condExp_mul_of_stronglyMeasurable_right _ _ _ using 1;
      · exact funext fun x => mul_comm _ _;
      · apply_rules [ StronglyMeasurable.sub, stronglyMeasurable_condExp ];
        exact MeasureTheory.StronglyMeasurable.mono ( MeasureTheory.stronglyMeasurable_condExp ) ( S.hHG );
      · exact hprod_int;
      · exact hL_int.sub hcondG_int;
    convert h_fubini using 1;
  have h_fubini : μ[L - μ[L | S.mG] | S.mG] =ᵐ[μ] 0 := by
    have h_fubini : μ[L - μ[L | S.mG] | S.mG] =ᵐ[μ] μ[L | S.mG] - μ[μ[L | S.mG] | S.mG] := by
      apply_rules [ MeasureTheory.condExp_sub ];
    have h_fubini : μ[μ[L | S.mG] | S.mG] =ᵐ[μ] μ[L | S.mG] := by
      apply_rules [ MeasureTheory.condExp_condExp_of_le ];
      · exact le_rfl;
      · exact le_trans S.hGK S.hK0;
    filter_upwards [ ‹μ[L - μ[L | S.mG] | S.mG] =ᶠ[ae μ] μ[L | S.mG] - μ[μ[L | S.mG] | S.mG]›, h_fubini ] with ω hω₁ hω₂ using by aesop;
  rw [ ‹∫ ω, ( L ω - μ[L | S.mG] ω ) * ( μ[L | S.mG] ω - μ[L | S.mH] ω ) ∂μ = ∫ ω, ( μ[L | S.mG] ω - μ[L | S.mH] ω ) * ( L ω - μ[L | S.mG] ω ) ∂μ›, ‹∫ ω, ( μ[L | S.mG] ω - μ[L | S.mH] ω ) * ( L ω - μ[L | S.mG] ω ) ∂μ = ∫ ω, ( μ[L | S.mG] ω - μ[L | S.mH] ω ) * μ[L - μ[L | S.mG] | S.mG] ω ∂μ›, MeasureTheory.integral_eq_zero_of_ae ] ; filter_upwards [ h_fubini ] with ω hω ; aesop

/-
Theorem 2.7 (Pythagorean identity for nested projections):
    ‖L - E[L|H]‖² = ‖L - E[L|G]‖² + ‖E[L|G] - E[L|H]‖²
where norms are L²(Q) norms, i.e., ‖f‖² = ∫ f² dμ.
-/
theorem nested_residuals_pythagorean
    (S : Setup Ω m₀ μ)
    (L : Ω → ℝ)
    (hL_Kmeas : @StronglyMeasurable Ω ℝ _ S.mK L)
    (hL_int : MeasureTheory.Integrable L μ)
    (hL_sq : MeasureTheory.Integrable (fun ω => L ω ^ 2) μ)
    (hcondG_int : MeasureTheory.Integrable (fun ω => μ[L | S.mG] ω) μ)
    (hcondH_int : MeasureTheory.Integrable (fun ω => μ[L | S.mH] ω) μ)
    (hcondG_sq : MeasureTheory.Integrable (fun ω => (μ[L | S.mG] ω) ^ 2) μ)
    (hcondH_sq : MeasureTheory.Integrable (fun ω => (μ[L | S.mH] ω) ^ 2) μ)
    (hprod_int : MeasureTheory.Integrable
      (fun ω => (L ω - μ[L | S.mG] ω) * (μ[L | S.mG] ω - μ[L | S.mH] ω)) μ)
    (h1 : MeasureTheory.Integrable
      (fun ω => (L ω - μ[L | S.mH] ω) ^ 2) μ)
    (h2 : MeasureTheory.Integrable
      (fun ω => (L ω - μ[L | S.mG] ω) ^ 2) μ)
    (h3 : MeasureTheory.Integrable
      (fun ω => (μ[L | S.mG] ω - μ[L | S.mH] ω) ^ 2) μ) :
    ∫ ω, (L ω - μ[L | S.mH] ω) ^ 2 ∂μ =
      ∫ ω, (L ω - μ[L | S.mG] ω) ^ 2 ∂μ +
      ∫ ω, (μ[L | S.mG] ω - μ[L | S.mH] ω) ^ 2 ∂μ := by
  -- Apply the orthogonal decomposition theorem to split the integral into two parts.
  have h_split : ∫ ω, ((L ω - μ[L | S.mG] ω) + (μ[L | S.mG] ω - μ[L | S.mH] ω)) ^ 2 ∂μ = (∫ ω, (L ω - μ[L | S.mG] ω) ^ 2 ∂μ) + 2 * (∫ ω, (L ω - μ[L | S.mG] ω) * (μ[L | S.mG] ω - μ[L | S.mH] ω) ∂μ) + (∫ ω, (μ[L | S.mG] ω - μ[L | S.mH] ω) ^ 2 ∂μ) := by
    rw [ ← MeasureTheory.integral_const_mul, ← MeasureTheory.integral_add, ← MeasureTheory.integral_add ];
    · exact congr_arg _ ( funext fun x => by ring );
    · exact MeasureTheory.Integrable.add h2 ( MeasureTheory.Integrable.const_mul hprod_int 2 );
    · exact h3;
    · exact h2;
    · exact hprod_int.const_mul _;
  have := nested_residuals_orthogonal S L hL_Kmeas hL_int hL_sq hcondG_int hcondH_int hprod_int; simp_all +decide [ mul_comm ] ;

/-! ## Theorem 5.1: Optimal visible hedge decomposition

For `S ⊆ L²(Q, H) ⊆ L²(Q, K)` and `L = E[X | K]`:
  ‖X - C_S(X)‖² = ‖L - C_S(L)‖² + ‖X - L‖²

The claim's total hedge error decomposes into the latent loading's
hedge error plus the claim component outside the Perron stress field.
-/

/-
Theorem 5.1 (orthogonality of hedge decomposition):
If `L_hedge` is K-measurable, then it is orthogonal in L²
to the residual `X - E[X|K]`:
  ∫ L_hedge · (X - E[X|K]) dμ = 0

This is because `X - E[X|K]` is orthogonal to all K-measurable
functions by the definition of conditional expectation.
-/
theorem visible_hedge_orthogonal
    (S : Setup Ω m₀ μ)
    (X : Ω → ℝ)
    (hX_int : MeasureTheory.Integrable X μ)
    (hX_sq : MeasureTheory.Integrable (fun ω => X ω ^ 2) μ)
    (L_hedge : Ω → ℝ)
    (hL_Kmeas : @StronglyMeasurable Ω ℝ _ S.mK L_hedge)
    (hL_int : MeasureTheory.Integrable L_hedge μ)
    (hprod : MeasureTheory.Integrable
      (fun ω => L_hedge ω * (X ω - μ[X | S.mK] ω)) μ) :
    ∫ ω, L_hedge ω * (X ω - μ[X | S.mK] ω) ∂μ = 0 := by
  convert MeasureTheory.integral_condExp ( S.hK0 ) using 1;
  any_goals exact S.hSigmaFiniteK;
  any_goals try infer_instance;
  any_goals exact fun ω => L_hedge ω * ( X ω - μ[X | S.mK] ω );
  · rw [ MeasureTheory.integral_condExp ];
    exact S.hK0;
  · have h_cond_exp : ∫ ω, L_hedge ω * (X ω - μ[X | S.mK] ω) ∂μ = ∫ ω, μ[L_hedge * (X - μ[X | S.mK]) | S.mK] ω ∂μ := by
      rw [ MeasureTheory.integral_condExp ];
      · rfl;
      · exact S.hK0;
    rw [ h_cond_exp, MeasureTheory.integral_congr_ae ];
    rw [ MeasureTheory.integral_zero ];
    have h_cond_exp : μ[L_hedge * (X - μ[X | S.mK]) | S.mK] =ᶠ[ae μ] L_hedge * μ[X - μ[X | S.mK] | S.mK] := by
      apply_rules [ MeasureTheory.condExp_mul_of_stronglyMeasurable_left ];
      exact hX_int.sub ( MeasureTheory.integrable_condExp );
    refine' h_cond_exp.trans _;
    have h_cond_exp : μ[X - μ[X | S.mK] | S.mK] =ᵐ[μ] fun _ => 0 := by
      have h_cond_exp : μ[X - μ[X | S.mK] | S.mK] =ᵐ[μ] μ[X | S.mK] - μ[μ[X | S.mK] | S.mK] := by
        apply_rules [ MeasureTheory.condExp_sub ];
        exact MeasureTheory.integrable_condExp;
      refine' h_cond_exp.trans _;
      have h_cond_exp : μ[μ[X | S.mK] | S.mK] =ᵐ[μ] μ[X | S.mK] := by
        apply_rules [ MeasureTheory.condExp_condExp_of_le ];
        · exact le_rfl;
        · exact S.hK0;
      filter_upwards [ h_cond_exp ] with ω hω using by simp +decide [ hω ] ;
    filter_upwards [ h_cond_exp ] with ω hω using by simp +decide [ hω ] ;

/-! ## Algebraic Pythagorean identity

The core algebraic identity underlying the three-part decomposition. -/

/-- The algebraic Pythagorean identity:
    (a - c)² = (a - b)² + (b - c)² + 2(a - b)(b - c) -/
theorem three_part_decomposition_sq
    (a b c : ℝ) :
    (a - c) ^ 2 = (a - b) ^ 2 + (b - c) ^ 2 + 2 * (a - b) * (b - c) := by
  ring

end PerronStress

end