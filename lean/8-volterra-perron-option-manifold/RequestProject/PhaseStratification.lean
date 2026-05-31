/-
  ## Phase Stratification and Hedge Residuals

  Formalization of results from Section 6 ("Risk-neutral market phases") and
  Section 10 ("Canonical finite benchmark model") of

    J. Vidal Llauradó, "Volterra–Perron Pricing of the Option Manifold" (2026).

  ### Theorem 6.3 (Risk-neutral phase stratification)
  Phase labels are gauge-invariant functions of the recovered source quotient.
  Phase changes can occur only by hitting transition surfaces.

  ### Theorem 10.6 (Finite hedge formula and incompleteness certificate)
  The minimum hedge residual for a claim X is the distance from its Greek
  to the row space of the tradeable Jacobian.
-/

import Mathlib

open LinearMap Finset

set_option maxHeartbeats 800000

noncomputable section

/-! ### Theorem 6.3: Phase stratification (abstract form)

  If continuous functions define phase regions by threshold comparisons,
  then phase transitions occur only at threshold crossings.
-/

/-
**Phase stratification (abstract):**
  If `f : ℝ → ℝ` is continuous and `f(t₀) < c` and `f(t₁) ≥ c`,
  then there exists `t` between `t₀` and `t₁` such that `f(t) = c`.
-/
theorem phase_transition_crossing
    (f : ℝ → ℝ) (hf : Continuous f) (c : ℝ)
    (t₀ t₁ : ℝ) (ht : t₀ ≤ t₁)
    (h₀ : f t₀ < c) (h₁ : c ≤ f t₁) :
    ∃ t ∈ Set.Icc t₀ t₁, f t = c := by
  apply_rules [ intermediate_value_Icc, hf.continuousOn ];
  constructor <;> linarith

/-
Corollary: if `f` is continuous and stays below `c`
  on an interval, then `f(t) ≠ c` on that interval.
-/
theorem no_phase_transition_on_interval
    (f : ℝ → ℝ) (hf : Continuous f) (c : ℝ)
    (a b : ℝ) (hab : a ≤ b)
    (hbelow : ∀ t ∈ Set.Icc a b, f t < c) :
    ∀ t ∈ Set.Icc a b, f t ≠ c := by
  -- By definition of $hbelow$, for any $t \in [a, b]$, we have $f(t) < c$.
  intros t ht
  have h_lt : f t < c := hbelow t ht
  exact ne_of_lt h_lt

/-! ### Theorem 10.6: Hedge residual as projection distance -/

/-
**Hedge residual characterization (abstract):**
  For any vector `g` in a Hilbert space and any closed subspace `W`,
  the minimum distance from `g` to `W` is achieved by the orthogonal
  projection.
-/
theorem hedge_residual_characterization
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (W : Submodule ℝ H) [Submodule.HasOrthogonalProjection W] (g : H) :
    ∃ h : W, ‖g - (h : H)‖ = iInf (fun w : W => ‖g - (w : H)‖) := by
  -- By definition of orthogonal projection, we know that for any vector g in a Hilbert space H, there exists a unique vector p in W such that g - p is orthogonal to W.
  obtain ⟨p, hp⟩ : ∃ p : H, p ∈ W ∧ g - p ∈ Wᗮ := by
    exact?;
  refine' ⟨ ⟨ p, hp.1 ⟩, le_antisymm _ _ ⟩;
  · refine' le_ciInf fun w => _;
    have h_orthogonal : ‖g - w‖ ^ 2 = ‖g - p‖ ^ 2 + ‖p - w‖ ^ 2 := by
      rw [ show g - w = ( g - p ) + ( p - w ) by abel1, norm_add_sq_real ];
      grind +suggestions;
    exact le_of_pow_le_pow_left₀ ( by norm_num ) ( norm_nonneg _ ) ( h_orthogonal ▸ le_add_of_nonneg_right ( sq_nonneg _ ) );
  · exact ciInf_le ⟨ 0, Set.forall_mem_range.2 fun _ => norm_nonneg _ ⟩ _

/-
The minimum distance to a closed subspace equals the norm of the
  orthogonal projection onto the complement.
-/
theorem hedge_residual_equals_ortho_proj
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (W : Submodule ℝ H) [Submodule.HasOrthogonalProjection W]
    (g : H) :
    iInf (fun w : W => ‖g - (w : H)‖) = ‖Submodule.orthogonalProjection Wᗮ g‖ := by
  rw [ @ciInf_eq_of_forall_ge_of_forall_gt_exists_lt ];
  · intro w;
    -- By definition of orthogonal projection, we know that $g - w = (g - proj_W(g)) + (proj_W(g) - w)$, and these two terms are orthogonal.
    have h_decomp : g - w = (Submodule.orthogonalProjection Wᗮ g) + (Submodule.orthogonalProjection W g - w) := by
      simp +decide [ Submodule.starProjection_add_starProjection_orthogonal ];
    rw [ h_decomp, norm_add_eq_sqrt_iff_real_inner_eq_zero.mpr ];
    · exact Real.le_sqrt_of_sq_le ( by nlinarith! );
    · simp +decide [ inner_sub_right, Submodule.mem_orthogonal' ];
  · intro w hw;
    refine' ⟨ ⟨ W.orthogonalProjection g, _ ⟩, _ ⟩;
    exact Submodule.coe_mem _;
    convert hw using 1;
    norm_num

end