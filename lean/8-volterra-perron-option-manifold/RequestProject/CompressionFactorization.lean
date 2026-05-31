/-
  ## Compression Factorization and Tower Property

  Formalization of Proposition 3.8 (Compression factorization of public prices),
  Lemma 5.9 (Public preservation), and Lemma 5.10 (Residual annihilator) from

    J. Vidal Llauradó, "Volterra–Perron Pricing of the Option Manifold" (2026).
-/

import Mathlib

open MeasureTheory

set_option maxHeartbeats 800000

/-! ### Lemma 5.10: Residual annihilator positivity

  If `|η| < ‖R‖_∞⁻¹`, then `1 + η · R > 0` a.e.
  This is the positivity condition for the density family Z = 1 + η R.
-/

/-
If `‖R‖_∞ ≤ M` and `|η| · M < 1`, then `1 + η * R(ω) > 0` for all ω
  where `|R(ω)| ≤ M`.
-/
theorem residual_density_positive
    (R : ℝ → ℝ) (η M : ℝ) (hM : 0 < M)
    (hbound : ∀ ω, |R ω| ≤ M)
    (hη : |η| * M < 1) :
    ∀ ω, 0 < 1 + η * R ω := by
  cases abs_cases η <;> intro ω <;> cases abs_cases ( R ω ) <;> nlinarith [ hbound ω ]

/-! ### Lemma 5.9: Public preservation (abstract version)

  If Y is constant and E[Z] = 1, then E[Z · Y] = Y.
  This is a simple consequence of linearity of expectation.
-/

/-
**Lemma 5.9 (simplified):**
  If `∫ Z dμ = 1` and `Y` is a constant, then `∫ Z * Y dμ = Y`.
-/
theorem public_preservation_simple
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (Z : Ω → ℝ) (Y : ℝ)
    (hZ : Integrable Z μ) (hZnorm : ∫ ω, Z ω ∂μ = 1) :
    ∫ ω, Z ω * Y ∂μ = Y := by
  rw [ MeasureTheory.integral_mul_const, hZnorm, one_mul ]

/-! ### Proposition 3.8: Compression factorization

  The tower property: E[E[X | K] | H] = E[X | H] when H ≤ K.
  We state this as: for σ-algebras m₁ ≤ m₂ on the same space,
  iterated conditional expectation telescopes.
-/

/-
**Proposition 3.8 (simplified unconditional form):**
  If `f` is integrable and `g = E[f | m₂]`, then `E[g | m₁] = E[f | m₁]`
  when `m₁ ≤ m₂`.

  In Mathlib this is `condexp_condexp_of_le`.
-/
theorem compression_factorization_statement
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω}
    (m₁ m₂ : MeasurableSpace Ω) (hle : m₁ ≤ m₂) (hle2 : m₂ ≤ mΩ)
    [SigmaFinite (μ.trim hle2)]
    [SigmaFinite (μ.trim (hle.trans hle2))]
    (f : Ω → ℝ) :
    μ[μ[f|m₂]|m₁] =ᵐ[μ] μ[f|m₁] := by
  convert MeasureTheory.condExp_condExp_of_le hle using 1;
  all_goals tauto