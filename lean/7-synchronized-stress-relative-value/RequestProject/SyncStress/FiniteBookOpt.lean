/-
# Theorem 5.6: Finite public-neutral book optimization

Existence and uniqueness of the optimizer for a concave objective on a
nonempty compact convex feasible set.

From: "Synchronized Stress Relative Value" by J. Vidal Llauradó (2026).
-/
import Mathlib

open scoped BigOperators

noncomputable section

/-! ## Theorem 5.6 (Finite public-neutral book optimization)

The book optimization maximizes `μᵀx - λ xᵀΣx - κ TC(x)` over a nonempty
compact convex feasible set. Existence follows from the Weierstrass theorem
(upper semicontinuous function on a compact set attains its supremum).
Uniqueness follows from strict concavity.

We formalize the core: an upper semicontinuous function on a nonempty compact
set attains its supremum, and a strictly concave function has at most one
maximizer on a convex set. -/

/-
**Theorem 5.6 (Existence).** An upper semicontinuous function on a nonempty
    compact set attains its supremum.
-/
theorem finite_book_existence {n : ℕ}
    (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (X : Set (EuclideanSpace ℝ (Fin n)))
    (hne : X.Nonempty) (hcpt : IsCompact X)
    (husc : UpperSemicontinuousOn f X) :
    ∃ x ∈ X, ∀ y ∈ X, f y ≤ f x := by
  by_contra h_contra;
  have h_least : ∀ x ∈ X, ∃ U : Set (EuclideanSpace ℝ (Fin n)), IsOpen U ∧ x ∈ U ∧ ∀ y ∈ U ∩ X, f y < f x + (SupSet.sSup (f '' X) - f x) / 2 := by
    intro x hx;
    have := husc x hx;
    have := this ( f x + ( SupSet.sSup ( f '' X ) - f x ) / 2 ) ( by linarith [ show f x < SupSet.sSup ( f '' X ) from lt_of_not_ge fun h => h_contra ⟨ x, hx, fun y hy => le_trans ( le_csSup ( show BddAbove ( f '' X ) from hcpt.image_of_continuousOn ( show ContinuousOn f X from by
                                                                                                                                                                                                                                                              exact False.elim <| h_contra ⟨ x, hx, fun y hy => by linarith [ h, le_csSup ( show BddAbove ( f '' X ) from by
                                                                                                                                                                                                                                                                                                                                              exact? ) <| Set.mem_image_of_mem f hy ] ⟩ ) |> IsCompact.bddAbove ) <| Set.mem_image_of_mem f hy ) h ⟩ ] );
    rcases mem_nhdsWithin.mp this with ⟨ U, hU₁, hU₂ ⟩;
    exact ⟨ U, hU₁, hU₂.1, fun y hy => hU₂.2 hy ⟩;
  choose! U hU using h_least;
  -- Since $X$ is compact, there exists a finite subset $F \subseteq X$ such that $X \subseteq \bigcup_{x \in F} U_x$.
  obtain ⟨F, hF⟩ : ∃ F : Finset (EuclideanSpace ℝ (Fin n)), (∀ x ∈ F, x ∈ X) ∧ X ⊆ ⋃ x ∈ F, U x := by
    have := hcpt.elim_nhds_subcover;
    exact this U fun x hx => IsOpen.mem_nhds ( hU x hx |>.1 ) ( hU x hx |>.2.1 );
  -- Let $M = \max_{x \in F} f(x)$.
  obtain ⟨M, hM⟩ : ∃ M ∈ f '' F, ∀ y ∈ f '' F, y ≤ M := by
    apply_rules [ Set.exists_max_image ];
    · exact F.finite_toSet.image f;
    · exact ⟨ _, Set.mem_image_of_mem f ( Classical.choose_spec ( Finset.nonempty_of_ne_empty ( by rintro rfl; exact hne.elim fun x hx => by simpa using hF.2 hx ) ) ) ⟩;
  -- Since $M$ is the maximum value of $f$ on $F$, we have $f(y) < M + (sSup (f '' X) - M) / 2$ for all $y \in X$.
  have h_bound : ∀ y ∈ X, f y < M + (sSup (f '' X) - M) / 2 := by
    intros y hy
    obtain ⟨x, hx⟩ : ∃ x ∈ F, y ∈ U x := by
      simpa using hF.2 hy;
    linarith [ hU x ( hF.1 x hx.1 ) |>.2.2 y ⟨ hx.2, hy ⟩, hM.2 ( f x ) ( Set.mem_image_of_mem f hx.1 ) ];
  -- Since $M$ is the maximum value of $f$ on $F$, we have $sSup (f '' X) \leq M + (sSup (f '' X) - M) / 2$.
  have h_sSup_bound : sSup (f '' X) ≤ M + (sSup (f '' X) - M) / 2 := by
    exact csSup_le ( Set.Nonempty.image _ hne ) ( Set.forall_mem_image.2 fun x hx => le_of_lt ( h_bound x hx ) );
  grind

/-
**Theorem 5.6 (Uniqueness).** A strictly concave function on a convex set
    has at most one maximizer.
-/
theorem finite_book_uniqueness {n : ℕ}
    (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (X : Set (EuclideanSpace ℝ (Fin n)))
    (hcvx : Convex ℝ X)
    (hsc : StrictConcaveOn ℝ X f)
    (x₁ x₂ : EuclideanSpace ℝ (Fin n))
    (hx₁ : x₁ ∈ X) (hx₂ : x₂ ∈ X)
    (hmax₁ : ∀ y ∈ X, f y ≤ f x₁)
    (hmax₂ : ∀ y ∈ X, f y ≤ f x₂) :
    x₁ = x₂ := by
  by_contra hmax₁;
  -- By strict concavity, $f(z) > \frac{1}{2}f(x_1) + \frac{1}{2}f(x_2)$ for $z = \frac{x_1 + x_2}{2}$.
  have h_strict : f ((1 / 2 : ℝ) • x₁ + (1 / 2 : ℝ) • x₂) > (1 / 2 : ℝ) * f x₁ + (1 / 2 : ℝ) * f x₂ := by
    exact hsc.2 hx₁ hx₂ hmax₁ ( by norm_num ) ( by norm_num ) ( by norm_num );
  linarith [ hmax₁, ‹∀ y ∈ X, f y ≤ f x₁› ( ( 1 / 2 : ℝ ) • x₁ + ( 1 / 2 : ℝ ) • x₂ ) ( hcvx hx₁ hx₂ ( by norm_num ) ( by norm_num ) ( by norm_num ) ), ‹∀ y ∈ X, f y ≤ f x₂› ( ( 1 / 2 : ℝ ) • x₁ + ( 1 / 2 : ℝ ) • x₂ ) ( hcvx hx₁ hx₂ ( by norm_num ) ( by norm_num ) ( by norm_num ) ) ]

end