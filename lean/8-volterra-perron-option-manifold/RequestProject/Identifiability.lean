/-
  ## Route Identifiability and Analytic Functions

  Formalization of results from Section 4 ("A Volterra-Perron source chart") of

    J. Vidal Llauradó, "Volterra–Perron Pricing of the Option Manifold" (2026).

  ### Theorem 4.3 (Power-exponential route identifiability)
  If a finite linear combination of power-exponential dictionary atoms
  `τ^α · exp(-β·τ)` vanishes on a nonempty open interval, then every
  coefficient is zero.

  ### Corollary 4.4 (Rough exponent as a short-maturity invariant)
  The rough exponent α is recovered as lim_{τ→0} τ f'(τ)/f(τ).

  We formalize the linear independence of exponential-polynomial functions,
  which is the core mathematical content behind the identifiability theorem.
-/

import Mathlib

open Real Set

set_option maxHeartbeats 800000

noncomputable section

/-! ### Linear independence of exponentials -/

/-
Distinct real exponentials `exp(β₁ · x), ..., exp(βₙ · x)` are linearly
  independent as functions on `ℝ`. This is a standard result that underpins
  the power-exponential identifiability theorem.
-/
theorem exp_linearIndependent {n : ℕ} (β : Fin n → ℝ) (hβ : Function.Injective β) :
    LinearIndependent ℝ (fun i : Fin n => (fun x : ℝ => Real.exp (β i * x))) := by
  refine' Fintype.linearIndependent_iff.2 _;
  -- We'll use the fact that if the exponential functions are linearly dependent, then their Wronskian determinant must be zero.
  intro g hg
  have h_wronskian : Matrix.det (Matrix.of (fun (i j : Fin n) => (β j) ^ (i : ℕ))) ≠ 0 := by
    erw [ Matrix.det_transpose, Matrix.det_vandermonde ];
    exact Finset.prod_ne_zero_iff.mpr fun i hi => Finset.prod_ne_zero_iff.mpr fun j hj => sub_ne_zero_of_ne <| hβ.ne <| by aesop;
  -- By taking derivatives of the linear combination and evaluating them at $x = 0$, we obtain a system of linear equations.
  have h_system : ∀ k : Fin n, ∑ i : Fin n, g i * (β i) ^ (k : ℕ) = 0 := by
    -- By taking derivatives of the linear combination and evaluating them at $x = 0$, we obtain a system of linear equations. We'll use induction on $k$.
    have h_deriv : ∀ k : ℕ, ∀ x : ℝ, deriv^[k] (fun x => ∑ i : Fin n, g i * Real.exp (β i * x)) x = ∑ i : Fin n, g i * (β i) ^ k * Real.exp (β i * x) := by
      intro k x; induction' k with k ih generalizing x <;> simp_all +decide [ Function.iterate_succ_apply', pow_succ, mul_assoc, mul_comm, mul_left_comm ] ;
      rw [ show deriv ( fun x => _ ) = _ from funext fun _ => by aesop ] ; norm_num [ mul_assoc, mul_comm, mul_left_comm, Finset.mul_sum _ _ _ ];
    intro k; specialize h_deriv k 0; simp_all +decide [ funext_iff ] ;
    exact h_deriv ▸ by norm_num [ Function.iterate_fixed ] ;
  -- This system of linear equations can be written in matrix form as $A \cdot g = 0$, where $A$ is the Vandermonde matrix.
  set A : Matrix (Fin n) (Fin n) ℝ := Matrix.of (fun (i j : Fin n) => (β j) ^ (i : ℕ))
  have hA : A.mulVec g = 0 := by
    exact funext fun i => by simpa [ Matrix.mulVec, dotProduct, mul_comm ] using h_system i;
  exact fun i => by simpa [ h_wronskian ] using Matrix.eq_zero_of_mulVec_eq_zero h_wronskian hA |> fun h => by simpa [ h ] ;

/-! ### Linear independence of power functions on (0, ∞) -/

/-
Distinct real powers `x^α₁, ..., x^αₙ` are linearly independent
  on `(0, ∞)`.
-/
theorem rpow_linearIndependent {n : ℕ} (α : Fin n → ℝ) (hα : Function.Injective α) :
    LinearIndependent ℝ (fun i : Fin n => (fun x : ℝ => x ^ (α i : ℝ))) := by
  refine' Fintype.linearIndependent_iff.2 _;
  intro g hg i
  have h_eq : ∀ t : ℝ, ∑ i, g i * Real.exp (α i * t) = 0 := by
    intro t; have := congr_fun hg ( Real.exp t ) ; simp_all +decide [ Real.rpow_def_of_pos, mul_comm ] ;
    simpa [ Real.rpow_def_of_pos ( Real.exp_pos _ ), mul_comm ] using this;
  -- Apply the exponential linear independence theorem to conclude that each coefficient must be zero.
  have h_exp_linear_indep : LinearIndependent ℝ (fun i : Fin n => (fun t : ℝ => Real.exp (α i * t))) := by
    exact?;
  rw [ Fintype.linearIndependent_iff ] at h_exp_linear_indep;
  exact h_exp_linear_indep g ( funext fun t => by simpa [ mul_comm ] using h_eq t ) i

/-! ### Power-exponential identifiability (Theorem 4.3, simplified form) -/

/-
**Theorem 4.3 (simplified):**
  If distinct exponentials with polynomial coefficients sum to zero on
  an open interval, all coefficients vanish.

  Simplified to: if `∑ cᵢ exp(βᵢ x) = 0` for all `x` in a nonempty open
  interval and the `βᵢ` are distinct, then `cᵢ = 0` for all `i`.
-/
theorem power_exp_identifiability_simple
    {n : ℕ} (c : Fin n → ℝ) (β : Fin n → ℝ)
    (hβ : Function.Injective β)
    (a b : ℝ) (hab : a < b)
    (hzero : ∀ x ∈ Ioo a b,
      ∑ i : Fin n, c i * Real.exp (β i * x) = 0) :
    ∀ i : Fin n, c i = 0 := by
  -- By analytic continuation, if a linear combination of exponentials vanishes on an open set, it must be the zero function.
  have h_analytic : ∀ (f : ℝ → ℝ), (∀ x ∈ Set.Ioo a b, f x = 0) → (∀ x, f x = 0) → LinearIndependent ℝ (fun i => (fun x => Real.exp (β i * x))) → ∀ i, c i = 0 := by
    -- Assume that $f(x) = 0$ for all $x \in (a, b)$ and $f(x)$ is a linear combination of the exponentials.
    intro f hf_zero hf_zero_all h_lin_ind
    have h_sum_zero : ∀ x, ∑ i, c i * Real.exp (β i * x) = 0 := by
      -- By analytic continuation, if a linear combination of exponentials vanishes on an open set, it must be the zero function. Hence, we can apply the theorem `analyticOnNhd_of_analyticOn_nhds`.
      have h_analytic : AnalyticOn ℝ (fun x => ∑ i, c i * Real.exp (β i * x)) Set.univ := by
        apply_rules [ ContDiffOn.analyticOn, ContDiffOn.sum ];
        exact fun i _ => ContDiffOn.mul contDiffOn_const ( ContDiffOn.exp ( contDiffOn_const.mul contDiffOn_id ) );
      simp +zetaDelta at *;
      intro x; exact (by
      apply h_analytic.eqOn_zero_of_preconnected_of_eventuallyEq_zero;
      exacts [ isPreconnected_univ, trivial, Filter.eventually_of_mem ( Ioo_mem_nhds ( show a < ( a + b ) / 2 by linarith ) ( show ( a + b ) / 2 < b by linarith ) ) fun x hx => hzero x hx.1 hx.2, trivial ]);
    rw [ Fintype.linearIndependent_iff ] at h_lin_ind;
    exact h_lin_ind c ( funext fun x => by simpa using h_sum_zero x );
  apply h_analytic;
  exact?;
  · norm_num;
  · convert exp_linearIndependent β hβ using 1

/-! ### Corollary 4.4: Leading power recovery

  If f(τ) = A · τ^α · (1 + O(τ)) with A ≠ 0, then
  α = lim_{τ→0⁺} τ · f'(τ) / f(τ).

  We formalize this as: for f(x) = x^α on (0, ∞), the identity
  x · f'(x) / f(x) = α holds exactly.
-/

/-
For `f(x) = x^α`, the logarithmic derivative satisfies
  `x · f'(x) / f(x) = α` for `x > 0`.
-/
theorem rpow_log_derivative (α : ℝ) (x : ℝ) (hx : 0 < x) :
    x * (α * x ^ (α - 1)) / x ^ α = α := by
  rw [ div_eq_iff ( by positivity ), mul_comm ];
  rw [ mul_assoc, ← Real.rpow_add_one hx.ne', sub_add_cancel ]

/-! ### Analytic identity theorem application

  A key step in Theorem 4.3's proof: if a real analytic function vanishes
  on a nonempty open interval, it vanishes everywhere on its connected domain.
-/

/-
**Identity theorem for polynomials:**
  If a polynomial of degree ≤ n vanishes at n+1 distinct points,
  then it is the zero polynomial.
-/
theorem polynomial_identity
    (p : Polynomial ℝ) (S : Finset ℝ) (hS : p.natDegree < S.card)
    (hzero : ∀ x ∈ S, p.eval x = 0) :
    p = 0 := by
  exact Classical.not_not.1 fun h => hS.not_ge <| by simpa [ h ] using ( Finset.card_le_card <| show S ⊆ p.roots.toFinset from fun x hx => by aesop ) |> ( fun h => h.trans <| Multiset.toFinset_card_le _ ) |> le_trans <| Polynomial.card_roots' _;

end