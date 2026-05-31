/-
# Proposition 5.5: Stress-convexity hedge ratio

The hedge ratio χ is the slope coefficient in a conditional least-squares regression.
This is the standard OLS characterization: Cov(X,Y)/Var(X) minimizes E[(Y - a - χX)²].

From: "Synchronized Stress Relative Value" by J. Vidal Llauradó (2026).
-/
import Mathlib

noncomputable section

/-! ## Proposition 5.5 (Stress-convexity hedge ratio)

We formalize the core mathematical fact: for random variables with finite
second moments, the slope `Cov(X,Y)/Var(X)` minimizes the expected squared
residual `E[(Y - a - χX)²]` over all `(a, χ)`.

We state this in a finite-sample (empirical) formulation to stay within
decidable Lean territory: given finite data vectors, the OLS slope minimizes
the sum of squared residuals. -/

/-- The OLS slope for finite data: `Σ(xᵢ - x̄)(yᵢ - ȳ) / Σ(xᵢ - x̄)²`. -/
def olsSlope {n : ℕ} (x y : Fin n → ℝ) : ℝ :=
  let x_bar := (∑ i, x i) / n
  let y_bar := (∑ i, y i) / n
  let cov := ∑ i, (x i - x_bar) * (y i - y_bar)
  let var_x := ∑ i, (x i - x_bar) ^ 2
  cov / var_x

/-- The OLS intercept: `ȳ - slope * x̄`. -/
def olsIntercept {n : ℕ} (x y : Fin n → ℝ) : ℝ :=
  let x_bar := (∑ i, x i) / n
  let y_bar := (∑ i, y i) / n
  y_bar - olsSlope x y * x_bar

/-- The sum of squared residuals for given `(a, χ)`. -/
def ssr {n : ℕ} (x y : Fin n → ℝ) (a chi : ℝ) : ℝ :=
  ∑ i, (y i - a - chi * x i) ^ 2

/-
**Proposition 5.5 (Stress-convexity hedge ratio).**
    When the sample variance of `x` is positive, the OLS slope and intercept
    minimize the sum of squared residuals.
-/
theorem stress_convexity_hedge_ratio {n : ℕ} (x y : Fin n → ℝ)
    (hvar : 0 < ∑ i, (x i - (∑ j, x j) / n) ^ 2) :
    ∀ a chi : ℝ, ssr x y (olsIntercept x y) (olsSlope x y) ≤ ssr x y a chi := by
  unfold ssr olsIntercept olsSlope;
  intro a chi;
  -- Expanding the sum of squared residuals, we can rewrite it as:
  have h_expand : ∑ i, (y i - a - chi * x i) ^ 2 = ∑ i, (y i - (∑ j, y j) / n - chi * (x i - (∑ j, x j) / n)) ^ 2 + n * ((∑ j, y j) / n - a - chi * (∑ j, x j) / n) ^ 2 := by
    simp +decide [ sub_sq, Finset.sum_add_distrib, Finset.mul_sum _ _ _, Finset.sum_mul _ _ _, mul_assoc, mul_comm, mul_left_comm, div_eq_mul_inv ] ; ring;
    by_cases hn : n = 0 <;> simp +decide [ hn, Finset.sum_add_distrib, Finset.mul_sum _ _ _, Finset.sum_mul _ _ _, mul_assoc, mul_comm, mul_left_comm, sq ] ; ring;
    · aesop;
    · simp +decide [ ← mul_assoc, ← Finset.mul_sum _ _ _, ← Finset.sum_mul, hn ] ; ring;
      -- Combine like terms and simplify the expression.
      field_simp
      ring;
  -- We can simplify the expression inside the sum:
  have h_simplify : ∑ i, (y i - (∑ j, y j) / n - chi * (x i - (∑ j, x j) / n)) ^ 2 = ∑ i, (y i - (∑ j, y j) / n) ^ 2 - 2 * chi * (∑ i, (x i - (∑ j, x j) / n) * (y i - (∑ j, y j) / n)) + chi ^ 2 * (∑ i, (x i - (∑ j, x j) / n) ^ 2) := by
    simp +decide only [sub_sq, mul_comm, mul_left_comm, mul_assoc, mul_pow, Finset.sum_add_distrib,
        Finset.sum_sub_distrib, Finset.mul_sum _ _ _];
    simp +decide only [mul_add, mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.mul_sum _ _ _];
  have h_simplify : ∑ i, (y i - (∑ j, y j) / n - (∑ i, (x i - (∑ j, x j) / n) * (y i - (∑ j, y j) / n)) / (∑ i, (x i - (∑ j, x j) / n) ^ 2) * (x i - (∑ j, x j) / n)) ^ 2 = ∑ i, (y i - (∑ j, y j) / n) ^ 2 - (∑ i, (x i - (∑ j, x j) / n) * (y i - (∑ j, y j) / n)) ^ 2 / (∑ i, (x i - (∑ j, x j) / n) ^ 2) := by
    have h_simplify : ∑ i, (y i - (∑ j, y j) / n - (∑ i, (x i - (∑ j, x j) / n) * (y i - (∑ j, y j) / n)) / (∑ i, (x i - (∑ j, x j) / n) ^ 2) * (x i - (∑ j, x j) / n)) ^ 2 = ∑ i, (y i - (∑ j, y j) / n) ^ 2 - 2 * ((∑ i, (x i - (∑ j, x j) / n) * (y i - (∑ j, y j) / n)) / (∑ i, (x i - (∑ j, x j) / n) ^ 2)) * (∑ i, (x i - (∑ j, x j) / n) * (y i - (∑ j, y j) / n)) + ((∑ i, (x i - (∑ j, x j) / n) * (y i - (∑ j, y j) / n)) / (∑ i, (x i - (∑ j, x j) / n) ^ 2)) ^ 2 * (∑ i, (x i - (∑ j, x j) / n) ^ 2) := by
      simp +decide [ sub_sq, Finset.sum_add_distrib, Finset.mul_sum _ _ _, Finset.sum_mul _ _ _, mul_assoc, mul_comm, mul_left_comm ];
      simp +decide [ ← Finset.sum_mul _ _ _, mul_pow ];
      simp +decide [ sub_sq, Finset.sum_add_distrib, Finset.mul_sum _ _ _, Finset.sum_mul _ _ _ ];
      exact Or.inl <| Finset.sum_congr rfl fun _ _ => by ring;
    grind +ring;
  have h_simplify : ∑ i, (y i - (∑ j, y j) / n - ((∑ i, (x i - (∑ j, x j) / n) * (y i - (∑ j, y j) / n)) / (∑ i, (x i - (∑ j, x j) / n) ^ 2)) * (x i - (∑ j, x j) / n)) ^ 2 ≤ ∑ i, (y i - (∑ j, y j) / n - chi * (x i - (∑ j, x j) / n)) ^ 2 := by
    nlinarith [ sq_nonneg ( chi * ( ∑ i, ( x i - ( ∑ j, x j ) / n ) ^ 2 ) - ( ∑ i, ( x i - ( ∑ j, x j ) / n ) * ( y i - ( ∑ j, y j ) / n ) ) ), mul_div_cancel₀ ( ( ∑ i, ( x i - ( ∑ j, x j ) / n ) * ( y i - ( ∑ j, y j ) / n ) ) ^ 2 ) hvar.ne', mul_div_cancel₀ ( ( ∑ i, ( x i - ( ∑ j, x j ) / n ) * ( y i - ( ∑ j, y j ) / n ) ) ) hvar.ne' ];
  convert h_simplify.trans ( le_add_of_nonneg_right <| mul_nonneg ( Nat.cast_nonneg _ ) <| sq_nonneg _ ) using 1;
  rotate_left 1;
  convert h_expand using 1;
  exact Finset.sum_congr rfl fun _ _ => by ring;

end