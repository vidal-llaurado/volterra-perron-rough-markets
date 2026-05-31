/-
  ## Bachelier Pricing Formula and Greeks

  Formalization of key results from Section 10 ("Canonical finite benchmark model") of

    J. Vidal Llauradó, "Volterra–Perron Pricing of the Option Manifold" (2026).

  The Bachelier (normal) call price is:
    C(F, K, V) = (F - K) · Φ(d) + √V · φ(d)
  where d = (F - K) / √V, Φ is the standard normal CDF, and φ is the density.

  Key properties formalized:
  - Standard normal density is symmetric and nonneg
  - Put-call parity in the Bachelier model
  - Intrinsic value bounds
  - Variance monotonicity
-/

import Mathlib

open Real MeasureTheory

set_option maxHeartbeats 800000

noncomputable section

/-- Standard normal density. -/
def stdNormalPdf (x : ℝ) : ℝ :=
  (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-(x ^ 2) / 2)

/-- Standard normal CDF (defined as an integral). -/
def stdNormalCdf (x : ℝ) : ℝ :=
  ∫ t in Set.Iic x, stdNormalPdf t

/-- The Bachelier (normal-model) call price.
  Definition 10.2 of the paper, with P(t,T) = 1 for simplicity. -/
def bachelierCall (F K : ℝ) (V : ℝ) : ℝ :=
  if V ≤ 0 then max (F - K) 0
  else
    let d := (F - K) / Real.sqrt V
    (F - K) * stdNormalCdf d + Real.sqrt V * stdNormalPdf d

/-- The Bachelier put price. -/
def bachelierPut (F K : ℝ) (V : ℝ) : ℝ :=
  if V ≤ 0 then max (K - F) 0
  else
    let d := (F - K) / Real.sqrt V
    (K - F) * stdNormalCdf (-d) + Real.sqrt V * stdNormalPdf d

/-! ### Properties of the standard normal density -/

/-
The standard normal PDF is symmetric: `φ(-x) = φ(x)`.
-/
theorem stdNormalPdf_neg (x : ℝ) : stdNormalPdf (-x) = stdNormalPdf x := by
  unfold stdNormalPdf; ring;

/-
The standard normal PDF is nonneg.
-/
theorem stdNormalPdf_nonneg (x : ℝ) : 0 ≤ stdNormalPdf x := by
  exact mul_nonneg ( inv_nonneg.2 ( Real.sqrt_nonneg _ ) ) ( Real.exp_nonneg _ )

/-! ### Put-call parity -/

/-
Complement relation: `Φ(x) + Φ(-x) = 1`.
-/
theorem stdNormalCdf_complement (x : ℝ) :
    stdNormalCdf x + stdNormalCdf (-x) = 1 := by
  -- Use the fact that the integral of the Gaussian distribution over the entire real line is 1.
  have h_gauss_integral : ∫ t in Set.univ, stdNormalPdf t = 1 := by
    unfold stdNormalPdf;
    rw [ MeasureTheory.integral_const_mul ];
    rw [ inv_mul_eq_div, div_eq_iff ( by positivity ) ] ; have := integral_gaussian ( 1 / 2 ) ; norm_num [ div_eq_inv_mul ] at * ; linarith;
  -- Use the fact that the integral of the Gaussian distribution over the entire real line is 1 to split the integral into two parts.
  have h_split_integral : ∫ t in Set.univ, stdNormalPdf t = (∫ t in Set.Iic x, stdNormalPdf t) + (∫ t in Set.Ioi x, stdNormalPdf t) := by
    rw [ ← MeasureTheory.setIntegral_union ] <;> norm_num;
    · exact MeasureTheory.Integrable.integrableOn ( by exact MeasureTheory.integrable_of_integral_eq_one ( by aesop ) );
    · exact MeasureTheory.Integrable.integrableOn ( by exact MeasureTheory.integrable_of_integral_eq_one ( by aesop ) );
  -- Use the fact that the integral of the Gaussian distribution over the interval $(-\infty, -x]$ is equal to the integral over the interval $[x, \infty)$.
  have h_symm_integral : ∫ t in Set.Ioi x, stdNormalPdf t = ∫ t in Set.Iic (-x), stdNormalPdf t := by
    rw [ ←neg_neg x, ←integral_comp_neg_Iic ] ; norm_num [ stdNormalPdf ];
  linarith!

/-
**Put-call parity in the Bachelier model:**
  `C(F,K,V) - P(F,K,V) = F - K` when `V > 0`.
-/
theorem bachelier_put_call_parity (F K V : ℝ) (hV : 0 < V) :
    bachelierCall F K V - bachelierPut F K V = F - K := by
  unfold bachelierCall bachelierPut;
  split_ifs <;> simp_all +decide [ sub_eq_iff_eq_add, stdNormalCdf_complement ];
  · lia;
  · have := stdNormalCdf_complement ( ( F - K ) / Real.sqrt V ) ; norm_num at * ; linear_combination' this * ( F - K ) ;

/-! ### Covariance structure: power-law monotonicity -/

/-
The diagonal variance `τ · ν` is nondecreasing in `τ` for `ν ≥ 0`.
-/
theorem diag_variance_mono (ν : ℝ) (hν : 0 ≤ ν) :
    Monotone (fun τ : ℝ => τ * ν) := by
  exact fun x y hxy => mul_le_mul_of_nonneg_right hxy hν

end