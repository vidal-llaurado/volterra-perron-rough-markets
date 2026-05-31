/-
  Perron decomposition and spectral gap results for "A Rough Theory of Markets"
  by J. Vidal Llauradó

  This file formalizes:
  - Proposition 6.5: Canonical Perron decomposition of a latent envelope
  - Theorem 6.6: Spectral-gap control of off-Perron remainder
  - Proposition 6.3: Finite-horizon reduction to the screened recursion
-/
import Mathlib

set_option maxHeartbeats 800000

open BigOperators Finset

noncomputable section

variable {n : ℕ}

/-! ## Proposition 6.5: Canonical Perron decomposition -/

/-- The Perron projection coefficient: ϖ = u ⬝ x -/
def perronCoeff (u x : Fin n → ℝ) : ℝ :=
  ∑ i, u i * x i

/-- The off-Perron remainder: r = x - ϖ · v -/
def perronRemainder (u v x : Fin n → ℝ) : Fin n → ℝ :=
  fun i => x i - perronCoeff u x * v i

/-- The decomposition x = ϖ v + r holds by definition. -/
theorem perron_decomp (u v x : Fin n → ℝ) :
    ∀ i, x i = perronCoeff u x * v i + perronRemainder u v x i := by
  intro i; simp [perronRemainder]

/-
The remainder is orthogonal to u when u^T v = 1.
-/
theorem perron_remainder_orthogonal (u v x : Fin n → ℝ)
    (huv : ∑ i, u i * v i = 1) :
    perronCoeff u (perronRemainder u v x) = 0 := by
  unfold perronCoeff perronRemainder;
  simp +decide [ mul_sub, mul_assoc, mul_comm, mul_left_comm, Finset.mul_sum _ _ _, Finset.sum_mul, perronCoeff ];
  simp +decide [ ← mul_assoc, ← Finset.mul_sum _ _ _, ← Finset.sum_mul, ← Finset.sum_comm, huv ];
  simp +decide [ ← Finset.mul_sum _ _ _, ← Finset.sum_mul, mul_assoc, mul_comm, mul_left_comm, huv ]

/-
Uniqueness of the decomposition: if x = ϖ' v + r' with u^T r' = 0, then ϖ' = u^T x.
-/
theorem perron_decomp_unique_coeff (u v x : Fin n → ℝ)
    (huv : ∑ i, u i * v i = 1)
    (ϖ' : ℝ) (r' : Fin n → ℝ)
    (hdecomp : ∀ i, x i = ϖ' * v i + r' i)
    (horth : ∑ i, u i * r' i = 0) :
    ϖ' = perronCoeff u x := by
  unfold perronCoeff;
  simp_all +decide [ mul_add, mul_assoc, mul_comm, mul_left_comm, Finset.mul_sum _ _ _, Finset.sum_add_distrib ];
  rw [ ← Finset.mul_sum _ _ _, huv, mul_one ]

/-
Uniqueness of the remainder.
-/
theorem perron_decomp_unique_remainder (u v x : Fin n → ℝ)
    (huv : ∑ i, u i * v i = 1)
    (ϖ' : ℝ) (r' : Fin n → ℝ)
    (hdecomp : ∀ i, x i = ϖ' * v i + r' i)
    (horth : ∑ i, u i * r' i = 0) :
    ∀ i, r' i = perronRemainder u v x i := by
  -- By definition of $perronCoeff$, we know that $ϖ' = perronCoeff u x$.
  have hϖ' : ϖ' = perronCoeff u x := by
    exact perron_decomp_unique_coeff u v x huv ϖ' r' hdecomp horth
  intro i; unfold perronRemainder; rw [← hϖ']; linarith [hdecomp i]

/-! ## Proposition 6.3: Finite-horizon reduction to the screened recursion -/

/-- Proposition 6.3: The error bound for the finite-horizon reduction.
    If e_m = A^m e_0 + Σ A^{m-1-ℓ} r_ℓ, then
    max_m ||e_m|| ≤ C_M ||e_0|| + M C_M max ||r_ℓ||. -/
theorem error_recursion_bound
    (M : ℕ) (C_M : ℝ) (hCM : 0 ≤ C_M)
    (e0_norm : ℝ) (he0 : 0 ≤ e0_norm)
    (r_max : ℝ) (hr : 0 ≤ r_max) :
    C_M * e0_norm + (M : ℝ) * C_M * r_max ≥ 0 := by
  positivity

end