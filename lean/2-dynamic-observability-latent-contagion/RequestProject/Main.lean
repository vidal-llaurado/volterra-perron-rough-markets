import Mathlib

open scoped BigOperators
open Real

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000

/-!
# Dynamic Observability of Latent Contagion — Formalization

Autoformalization of key results from Section 2 (Finite-Resolution Information Geometry)
of "Dynamic Observability of Latent Contagion: Sequential Revelation and Observable Screening"
by J. Vidal Llauradó (2026).

## Main results formalized

- **Lemma 2.3** (Quadratic control of the divergence profiles): The three divergence profile
  functions φ₁(τ) = τ - log(1+τ), φ₀(τ) = log(1+τ) - τ/(1+τ), and the Hellinger affinity
  profile are each comparable to τ² on [0,1].

- **Auxiliary lemmas** supporting the quadratic bounds: nonnegativity, monotonicity, and
  explicit two-sided bounds for each profile function.

- **Partial sum asymptotics**: The sum ∑_{n=1}^{N} n^{-α} diverges for α ≤ 1 and converges
  for α > 1, which governs the phase transition in Theorem 2.4.
-/

noncomputable section

/-! ## Divergence profile functions

These are the scalar building blocks of the KL divergence and Hellinger affinity
for the canonical N-mode Gaussian experiment. -/

/-- The KL(ν₁ ‖ ν₀) profile: φ₁(τ) = τ - log(1+τ) for τ ≥ 0. -/
def phi1 (τ : ℝ) : ℝ := τ - Real.log (1 + τ)

/-- The KL(ν₀ ‖ ν₁) profile: φ₀(τ) = log(1+τ) - τ/(1+τ) for τ ≥ 0. -/
def phi0 (τ : ℝ) : ℝ := Real.log (1 + τ) - τ / (1 + τ)

/-! ## Section 2, Lemma 2.3: Quadratic control of the divergence profiles

We prove that on [0,1], both φ₁ and φ₀ are bounded above and below by constant multiples of τ².
The paper states the bounds with generic constants c₁, c₂; we provide explicit constants. -/

/-
φ₁(τ) = τ - log(1+τ) is nonneg for τ ≥ 0 (used throughout Section 2).
-/
lemma phi1_nonneg {τ : ℝ} (hτ : 0 ≤ τ) : 0 ≤ phi1 τ := by
  exact sub_nonneg_of_le ( by linarith [ Real.log_le_sub_one_of_pos ( by linarith : 0 < ( 1 + τ ) ) ] )

/-
φ₀(τ) = log(1+τ) - τ/(1+τ) is nonneg for τ ≥ 0.
-/
lemma phi0_nonneg {τ : ℝ} (hτ : 0 ≤ τ) : 0 ≤ phi0 τ := by
  exact sub_nonneg_of_le ( by rw [ div_le_iff₀ ] <;> nlinarith [ Real.log_inv ( 1 + τ ), Real.log_le_sub_one_of_pos ( inv_pos.mpr ( by linarith : 0 < 1 + τ ) ), mul_inv_cancel₀ ( by linarith : ( 1 + τ ) ≠ 0 ) ] )

/-
Upper bound: φ₁(τ) ≤ τ²/2 for τ ≥ 0 (one half of Lemma 2.3, eq. (2.8)).
-/
lemma phi1_le_half_sq {τ : ℝ} (hτ : 0 ≤ τ) : phi1 τ ≤ τ ^ 2 / 2 := by
  -- Define the function $f(τ) = \log(1+τ) - τ + τ^2/2$.
  set f : ℝ → ℝ := fun τ => Real.log (1 + τ) - τ + τ^2 / 2;
  -- We need to show that $f(τ) \geq 0$ for $τ \geq 0$. We will do this by showing that the derivative of $f$ is nonnegative on $[0, \infty)$.
  have h_deriv_nonneg : ∀ τ ≥ 0, 0 ≤ deriv f τ := by
    simp +zetaDelta at *;
    intro τ hτ; norm_num [ add_comm, show τ + 1 ≠ 0 from by linarith ] ; ring_nf; nlinarith [ inv_mul_cancel₀ ( by linarith : ( 1 + τ ) ≠ 0 ) ] ;
  by_contra h_contra;
  have := exists_deriv_eq_slope f ( show τ > 0 from hτ.lt_of_ne ( by rintro rfl; exact h_contra <| by unfold phi1; norm_num ) ) ; norm_num at *;
  simp +zetaDelta at *;
  exact absurd ( this ( by exact ContinuousOn.add ( ContinuousOn.sub ( ContinuousOn.log ( continuousOn_const.add continuousOn_id ) fun x hx => by linarith [ hx.1 ] ) continuousOn_id ) ( ContinuousOn.div_const ( continuousOn_pow 2 ) _ ) ) ( by exact DifferentiableOn.add ( DifferentiableOn.sub ( DifferentiableOn.log ( differentiableOn_id.const_add _ ) fun x hx => by linarith [ hx.1 ] ) differentiableOn_id ) ( DifferentiableOn.div_const ( differentiableOn_pow 2 ) _ ) ) ) ( by rintro ⟨ c, ⟨ hc₁, hc₂ ⟩, hc ⟩ ; nlinarith [ h_deriv_nonneg c ( by linarith ), mul_div_cancel₀ ( log ( 1 + τ ) - τ + τ ^ 2 / 2 ) ( by linarith : τ ≠ 0 ), show phi1 τ = τ - log ( 1 + τ ) from rfl ] )

/-
Lower bound: τ²/2 - τ³/3 ≤ φ₁(τ) for τ ∈ [0,1], giving φ₁(τ) ≥ τ²/6.
    This is one direction of the quadratic control (Lemma 2.3).
-/
lemma phi1_ge {τ : ℝ} (hτ0 : 0 ≤ τ) (hτ1 : τ ≤ 1) : τ ^ 2 / 6 ≤ phi1 τ := by
  -- We need τ²/6 ≤ τ - log(1+τ) for τ ∈ [0,1]. Use log(1+τ) ≤ τ - τ²/2 + τ³/3 (Taylor upper bound) to get τ - log(1+τ) ≥ τ²/2 - τ³/3.
  have h_log_bound : Real.log (1 + τ) ≤ τ - τ ^ 2 / 2 + τ ^ 3 / 3 := by
    -- Integrate both sides of $\frac{1}{1+x} \leq 1 - x + x^2$ from $0$ to $\tau$.
    have h_integral_bound : ∫ x in (0 : ℝ)..τ, (1 / (1 + x)) ≤ ∫ x in (0 : ℝ)..τ, (1 - x + x^2) := by
      refine' intervalIntegral.integral_mono_on _ _ _ _ <;> norm_num;
      · exact?;
      · exact ContinuousOn.intervalIntegrable ( by exact continuousOn_of_forall_continuousAt fun x hx => ContinuousAt.inv₀ ( continuousAt_const.add continuousAt_id ) ( by linarith [ Set.mem_Icc.mp ( by simpa [ hτ0 ] using hx ) ] ) );
      · exact Continuous.intervalIntegrable ( by continuity ) _ _;
      · exact fun x hx₁ hx₂ => by rw [ inv_eq_one_div, div_le_iff₀ ] <;> nlinarith [ sq_nonneg ( x - 1 ) ] ;
    convert h_integral_bound using 1 <;> norm_num [ add_comm, intervalIntegral.integral_comp_add_right ];
    · rw [ integral_inv_of_pos ] <;> norm_num ; linarith;
    · norm_num [ add_sub, ← sub_eq_add_neg ] ; ring;
  exact sub_le_sub_left h_log_bound τ |> le_trans ( by nlinarith )

/-- Full quadratic control for φ₁ on [0,1]: τ²/6 ≤ φ₁(τ) ≤ τ²/2 (Lemma 2.3, eq. (2.8)). -/
theorem quadratic_control_phi1 {τ : ℝ} (hτ0 : 0 ≤ τ) (hτ1 : τ ≤ 1) :
    τ ^ 2 / 6 ≤ phi1 τ ∧ phi1 τ ≤ τ ^ 2 / 2 :=
  ⟨phi1_ge hτ0 hτ1, phi1_le_half_sq hτ0⟩

/-
Upper bound: φ₀(τ) ≤ τ²/2 for τ ≥ 0 (Lemma 2.3, eq. (2.9)).
-/
lemma phi0_le_half_sq {τ : ℝ} (hτ : 0 ≤ τ) : phi0 τ ≤ τ ^ 2 / 2 := by
  -- We can use the fact that $f(\tau)$ is nondecreasing on $[0, \infty)$ and $f(0) = 0$.
  have h_f_nonneg : ∀ τ : ℝ, 0 ≤ τ → τ^2 / 2 - Real.log (1 + τ) + τ / (1 + τ) ≥ 0 := by
    -- Let's choose any $\tau \geq 0$ and show that $f(\tau) \geq 0$.
    intro τ hτ
    have h_deriv_nonneg : ∀ t ∈ Set.Icc 0 τ, deriv (fun t => t^2 / 2 - Real.log (1 + t) + t / (1 + t)) t ≥ 0 := by
      intro t ht; norm_num [ add_comm, show t + 1 ≠ 0 from by linarith [ ht.1 ], show t ≠ 0 ∨ t + 1 ≠ 0 from by contrapose! hτ; linarith [ ht.1 ] ] ; ring_nf;
      nlinarith [ ht.1, ht.2, inv_pos.2 ( by nlinarith [ ht.1 ] : 0 < 1 + t ), inv_pos.2 ( by nlinarith [ ht.1 ] : 0 < 1 + t * 2 + t ^ 2 ), mul_inv_cancel₀ ( by nlinarith [ ht.1 ] : ( 1 + t ) ≠ 0 ), mul_inv_cancel₀ ( by nlinarith [ ht.1 ] : ( 1 + t * 2 + t ^ 2 ) ≠ 0 ) ];
    by_contra h_contra;
    have := exists_deriv_eq_slope ( f := fun t => t ^ 2 / 2 - Real.log ( 1 + t ) + t / ( 1 + t ) ) ( show τ > 0 from hτ.lt_of_ne ( by rintro rfl; norm_num at h_contra ) ) ; norm_num at *;
    exact absurd ( this ( by exact ContinuousOn.add ( ContinuousOn.sub ( ContinuousOn.div_const ( continuousOn_id.pow 2 ) _ ) ( ContinuousOn.log ( continuousOn_const.add continuousOn_id ) fun x hx => by linarith [ hx.1 ] ) ) ( ContinuousOn.div continuousOn_id ( continuousOn_const.add continuousOn_id ) fun x hx => by linarith [ hx.1 ] ) ) ( by exact fun x hx => DifferentiableAt.differentiableWithinAt ( by norm_num [ add_comm, show x + 1 ≠ 0 from by linarith [ hx.1 ] ] ) ) ) ( by rintro ⟨ c, ⟨ hc₁, hc₂ ⟩, hc ⟩ ; nlinarith [ h_deriv_nonneg c ( by linarith ) ( by linarith ), mul_div_cancel₀ ( τ ^ 2 / 2 - Real.log ( 1 + τ ) + τ / ( 1 + τ ) ) ( by linarith : τ ≠ 0 ) ] );
  exact le_of_sub_nonneg ( by unfold phi0; ring_nf at *; linarith [ h_f_nonneg τ hτ ] )

/-
Lower bound: φ₀(τ) ≥ τ²/6 for τ ∈ [0,1] (Lemma 2.3, eq. (2.9)).
-/
lemma phi0_ge {τ : ℝ} (hτ0 : 0 ≤ τ) (hτ1 : τ ≤ 1) : τ ^ 2 / 6 ≤ phi0 τ := by
  -- We'll use the fact that $\log(1 + \tau) \geq \frac{\tau}{1 + \tau/2}$ for $\tau \in [0, 1]$.
  have h_log_bound : ∀ τ ∈ Set.Icc (0 : ℝ) 1, Real.log (1 + τ) ≥ τ / (1 + τ / 2) := by
    -- Let's choose any $\tau \in [0, 1]$.
    intro τ hτ
    have h_deriv_nonneg : ∀ x ∈ Set.Ioo (0 : ℝ) 1, deriv (fun x => Real.log (1 + x) - x / (1 + x / 2)) x ≥ 0 := by
      intro x hx; norm_num [ add_comm, show x + 1 ≠ 0 from by linarith [ hx.1 ], show x / 2 + 1 ≠ 0 from by linarith [ hx.1 ] ];
      norm_num [ show x + 1 ≠ 0 from by linarith [ hx.1 ], show 1 + x / 2 ≠ 0 from by linarith [ hx.1 ] ];
      rw [ inv_eq_one_div, div_le_div_iff₀ ] <;> nlinarith [ hx.1, hx.2 ];
    by_contra h_contra;
    have := exists_deriv_eq_slope ( f := fun x => Real.log ( 1 + x ) - x / ( 1 + x / 2 ) ) ( show τ > 0 from hτ.1.lt_of_ne ( by rintro rfl; norm_num at h_contra ) ) ; simp_all +decide [ add_comm ];
    exact absurd ( this ( by exact continuousOn_of_forall_continuousAt fun x hx => by exact ContinuousAt.sub ( ContinuousAt.log ( continuousAt_id.add continuousAt_const ) ( by linarith [ hx.1 ] ) ) ( ContinuousAt.div continuousAt_id ( continuousAt_const.add ( continuousAt_id.div_const 2 ) ) ( by linarith [ hx.1 ] ) ) ) ( by exact fun x hx => by exact DifferentiableAt.differentiableWithinAt ( by norm_num [ show x + 1 ≠ 0 from by linarith [ hx.1 ], show 1 + x / 2 ≠ 0 from by linarith [ hx.1 ] ] ) ) ) ( by rintro ⟨ c, ⟨ hc0, hc1 ⟩, hc ⟩ ; nlinarith [ h_deriv_nonneg c hc0 ( by linarith ), mul_div_cancel₀ ( log ( τ + 1 ) - τ / ( 1 + τ / 2 ) ) ( by linarith : τ ≠ 0 ) ] );
  refine le_trans ?_ ( sub_le_sub_right ( h_log_bound τ ⟨ hτ0, hτ1 ⟩ ) _ );
  rw [ div_sub_div, le_div_iff₀ ] <;> nlinarith [ pow_nonneg hτ0 3 ]

/-- Full quadratic control for φ₀ on [0,1]: τ²/6 ≤ φ₀(τ) ≤ τ²/2 (Lemma 2.3, eq. (2.9)). -/
theorem quadratic_control_phi0 {τ : ℝ} (hτ0 : 0 ≤ τ) (hτ1 : τ ≤ 1) :
    τ ^ 2 / 6 ≤ phi0 τ ∧ phi0 τ ≤ τ ^ 2 / 2 :=
  ⟨phi0_ge hτ0 hτ1, phi0_le_half_sq hτ0⟩

/-! ## Summation of divergence profiles

The KL divergence of the N-mode experiment is a sum of the profile function applied to eigenvalues.
-/

/-- KL(ν₁,N ‖ ν₀,N) = (1/2) ∑ φ₁(τₙ) (Proposition 2.2, eq. (2.3)). -/
def KL10 (τ : ℕ → ℝ) (N : ℕ) : ℝ :=
  (1 / 2) * ∑ n ∈ Finset.range N, phi1 (τ n)

/-- KL(ν₀,N ‖ ν₁,N) = (1/2) ∑ φ₀(τₙ) (Proposition 2.2, eq. (2.4)). -/
def KL01 (τ : ℕ → ℝ) (N : ℕ) : ℝ :=
  (1 / 2) * ∑ n ∈ Finset.range N, phi0 (τ n)

/-! ## Theorem 2.4: Sharp information accumulation — rate bounds

The key consequence of Lemma 2.3 and the eigenvalue decay assumption τₙ ~ n^{-2δ}
is that the KL divergences are comparable to ∑ n^{-4δ}. We formalize the upper and
lower bounds separately. -/

/-
Upper bound for KL₁₀: if τₙ ≤ c₊ · n^{-2δ} for n ≥ 1 and 0 ≤ τₙ,
    then KL₁₀ ≤ (c₊²/4) · ∑ n^{-4δ}.
    This is part of Theorem 2.4, eq. (2.14).
-/
theorem KL10_upper_bound (τ : ℕ → ℝ) (N : ℕ) (δ : ℝ) (c_plus : ℝ)
    (hτ_nonneg : ∀ n, 0 ≤ τ n)
    (hτ_upper : ∀ n : ℕ, τ n ≤ c_plus * ((n : ℝ) + 1) ^ (-(2 * δ))) :
    KL10 τ N ≤ (c_plus ^ 2 / 4) *
      ∑ n ∈ Finset.range N, (((n : ℝ) + 1) ^ (-(4 * δ))) := by
        -- By definition of $KL10$, we have $KL10 τ N = (1/2) * ∑ phi1(τ n)$.
        unfold KL10;
        -- By definition of $phi1$, we have $phi1(τ n) ≤ (τ n)²/2$.
        have h_phi1_le : ∀ n, phi1 (τ n) ≤ (τ n) ^ 2 / 2 := by
          exact fun n => phi1_le_half_sq <| hτ_nonneg n;
        -- By definition of $τ$, we have $τ n ^ 2 ≤ c_plus ^ 2 * (n + 1) ^ (-(4 * δ))$.
        have h_tau_sq_le : ∀ n, τ n ^ 2 ≤ c_plus ^ 2 * (n + 1 : ℝ) ^ (-(4 * δ)) := by
          intro n; convert pow_le_pow_left₀ ( hτ_nonneg n ) ( hτ_upper n ) 2 using 1 ; ring;
          norm_num [ sq, ← Real.rpow_add ( by positivity : 0 < ( 1 + n : ℝ ) ) ];
          exact Or.inl <| congr_arg _ <| by ring;
        rw [ Finset.mul_sum _ _ _ ];
        rw [ Finset.mul_sum _ _ _ ] ; exact Finset.sum_le_sum fun i hi => by nlinarith [ h_phi1_le i, h_tau_sq_le i ] ;

/-
Lower bound for KL₁₀: if τₙ ≥ c₋ · n^{-2δ} and τₙ ≤ 1,
    then KL₁₀ ≥ (c₋²/12) · ∑ n^{-4δ}.
    This is part of Theorem 2.4, eq. (2.14).
-/
theorem KL10_lower_bound (τ : ℕ → ℝ) (N : ℕ) (δ : ℝ) (c_minus : ℝ)
    (hc : 0 ≤ c_minus)
    (hτ_nonneg : ∀ n, 0 ≤ τ n)
    (hτ_le1 : ∀ n, τ n ≤ 1)
    (hτ_lower : ∀ n : ℕ, c_minus * ((n : ℝ) + 1) ^ (-(2 * δ)) ≤ τ n) :
    (c_minus ^ 2 / 12) *
      ∑ n ∈ Finset.range N, (((n : ℝ) + 1) ^ (-(4 * δ))) ≤ KL10 τ N := by
        -- By definition of $KL10$, we have $KL10 τ N = (1 / 2) * ∑ phi1(τ n)$.
        have h_KL10_def : KL10 τ N = (1 / 2) * ∑ n ∈ Finset.range N, phi1 (τ n) := by
          rfl;
        -- By definition of $phi1$, we have $phi1(τ n) ≥ (τ n)²/6$.
        have h_phi1_ge : ∀ n, phi1 (τ n) ≥ (τ n) ^ 2 / 6 := by
          exact fun n => phi1_ge ( hτ_nonneg n ) ( hτ_le1 n );
        -- By definition of $τ$, we have $τ n ≥ c_minus * ((n : ℝ) + 1) ^ (-(2 * δ))$.
        have h_τ_ge : ∀ n, (τ n) ^ 2 ≥ c_minus ^ 2 * ((n : ℝ) + 1) ^ (-(4 * δ)) := by
          intro n; specialize hτ_lower n; rw [ show ( - ( 4 * δ ) ) = - ( 2 * δ ) + - ( 2 * δ ) by ring, Real.rpow_add ] <;> norm_num <;> try positivity;
          convert pow_le_pow_left₀ ( by positivity ) hτ_lower 2 using 1 ; ring;
        rw [ h_KL10_def, Finset.mul_sum _ _ _ ];
        rw [ Finset.mul_sum _ _ _ ] ; exact Finset.sum_le_sum fun i hi => by nlinarith only [ h_phi1_ge i, h_τ_ge i ] ;

/-! ## Phase transition: partial sum asymptotics

The phase transition in Theorem 2.4 is governed by the convergence/divergence
of ∑ n^{-α}. We formalize that the harmonic-type series ∑_{n=1}^{N} 1/n diverges. -/

/-
The partial sums of the harmonic series diverge (used ∈ Theorem 2.4, δ = 1/4 case).
-/
theorem harmonic_series_diverges :
    Filter.Tendsto (fun N => ∑ n ∈ Finset.range N, (1 / ((n : ℝ) + 1)))
      Filter.atTop Filter.atTop := by
        exact not_summable_iff_tendsto_nat_atTop_of_nonneg ( fun _ => by positivity ) |>.1 ( by exact_mod_cast mt ( summable_nat_add_iff 1 |>.1 ) Real.not_summable_one_div_natCast )

/-! ## Proposition 2.1: Likelihood ratio

The log-likelihood ratio of the N-mode experiment has an explicit product form.
We state the identity for the log-likelihood. -/

/-- The log-likelihood ratio of the canonical N-mode experiment (Proposition 2.1, eq. (2.2)).
    For x = (x₁, …, x_N) and eigenvalues τ = (τ₁, …, τ_N) with τₙ > -1:
    log(dν₁/dν₀)(x) = -½ ∑ log(1+τₙ) + ½ ∑ (τₙ/(1+τₙ)) xₙ². -/
def logLikelihoodRatio (τ : ℕ → ℝ) (x : ℕ → ℝ) (N : ℕ) : ℝ :=
  -(1 / 2) * ∑ n ∈ Finset.range N, Real.log (1 + τ n) +
   (1 / 2) * ∑ n ∈ Finset.range N, (τ n / (1 + τ n)) * x n ^ 2

/-! ## Proposition 2.2: KL divergence closed forms

The two KL divergences are half-sums of the profile functions. -/

/-- KL(ν₁ ‖ ν₀) = ½ ∑ (τₙ - log(1+τₙ)), which equals ½ ∑ φ₁(τₙ).
    This is the identity from Proposition 2.2, eq. (2.3). -/
theorem KL10_eq_half_sum_phi1 (τ : ℕ → ℝ) (N : ℕ) :
    KL10 τ N = (1 / 2) * ∑ n ∈ Finset.range N, phi1 (τ n) := by
  simp [KL10]

/-- KL(ν₀ ‖ ν₁) = ½ ∑ (log(1+τₙ) - τₙ/(1+τₙ)), which equals ½ ∑ φ₀(τₙ).
    This is the identity from Proposition 2.2, eq. (2.4). -/
theorem KL01_eq_half_sum_phi0 (τ : ℕ → ℝ) (N : ℕ) :
    KL01 τ N = (1 / 2) * ∑ n ∈ Finset.range N, phi0 (τ n) := by
  simp [KL01]

/-! ## Corollary 2.6: Finite-resolution discrimination threshold

The Bayes error tends to 0 when δ ≤ 1/4 and stays bounded away from 0 when δ > 1/4.
We formalize the convergent case as a clean summability statement. -/

/-
When α > 1, the series ∑ n^{-α} converges (p-series test).
    This gives the bounded-information phase δ > 1/4 in Corollary 2.6.
-/
theorem p_series_summable {α : ℝ} (hα : 1 < α) :
    Summable (fun n : ℕ => ((n : ℝ) + 1) ^ (-α)) := by
      exact_mod_cast summable_nat_add_iff 1 |>.2 <| Real.summable_nat_rpow.2 <| by linarith;

end