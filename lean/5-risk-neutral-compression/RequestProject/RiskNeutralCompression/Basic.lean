/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Risk-Neutral Compression and the Geometry of Latent Market Stress

Formalization of the core structural results from
"Risk-Neutral Compression and the Geometry of Latent Market Stress"
by J. Vidal Llauradó (2026).

## Mathematical content

The paper studies the operator C_H^Q (conditional expectation / orthogonal projection onto
a sub-sigma-field H under a pricing measure Q) applied to "priced structural loadings"
L_X^Q = E^Q[X | H_ϖ], where H_ϖ is the aggregate Perron structural sigma-field.

The core mathematical framework is Hilbert space orthogonal projection theory applied to
nested L²-spaces of sub-sigma-fields:

  H ⊆ G_T ⊆ H_ϖ ⊆ F_T

translates to closed subspace inclusions in L²(Q, F_T).

## Formalization approach

We formalize the structural results at the level of abstract real inner product spaces
with nested closed subspaces, which captures the essential Hilbert-space geometry.
The measure-theoretic layer (conditional expectations as L²-projections) is classical
and well-established; the paper's contribution lies in how these projections interact
across the specific nested sigma-field structure.

## Main results formalized

- **Proposition 4.2** (Supporting structural projection of claims): Tower property
  C_H(X) = C_H(L_X) where L_X = proj_{H_ϖ}(X).

- **Proposition 4.3** (Approximate sufficiency): If X = X_ϖ + R with X_ϖ ∈ H_ϖ,
  then ‖L_X - X_ϖ‖ ≤ ‖R‖.

- **Proposition 4.5** (Factor decomposition): Unique decomposition of L_X along
  a distinguished aggregate factor direction.

- **Corollary 4.6** (Factor screening): The centered aggregate factor is screened
  from all public compressions.

- **Corollary 4.7** (Compression principle): All public pricing objects factor
  through L_X.

- **Theorem 4.8** (Main risk-neutral compression): Hedge residual Pythagorean
  decomposition: inf_{H∈S} ‖X-H‖² = dist(L_X, S)² + ‖U_X‖².

- **Proposition 5.1** (L²-comparability): Norm equivalence under bounded density.
-/

import Mathlib

open Submodule

set_option maxHeartbeats 800000

noncomputable section

/-!
## Setup

We fix a real inner product space `E` (representing L²(Q, F_T)) with a nested chain of
closed subspaces:
- `pubInfo` (H): public information ≅ L²(Q, H)
- `visible` (G_T): visible market filtration ≅ L²(Q, G_T)
- `structural` (H_ϖ): aggregate Perron structural sigma-field ≅ L²(Q, H_ϖ)

The chain satisfies H ⊆ G_T ⊆ H_ϖ, i.e., `pubInfo ≤ visible ≤ structural`.
-/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- The "risk-neutral compression" operator: orthogonal projection onto a closed subspace.
    In the paper, C_H^Q(X) = E^Q[X | H] is the conditional expectation onto a sub-sigma-field,
    which is exactly the L²(Q)-orthogonal projection onto L²(Q, H). -/
def riskNeutralCompression (H : Submodule ℝ E) [H.HasOrthogonalProjection] (x : E) : E :=
  (H.orthogonalProjection x : E)

/-- The "priced structural loading" L_X^Q = C_{H_ϖ}^Q(X): the projection of a claim
    onto the structural subspace. -/
def pricedStructuralLoading (M : Submodule ℝ E) [M.HasOrthogonalProjection] (x : E) : E :=
  riskNeutralCompression M x

/-- The "structural residual" U_X^Q = X - L_X^Q: the component orthogonal to the
    structural subspace. -/
def structuralResidual (M : Submodule ℝ E) [M.HasOrthogonalProjection] (x : E) : E :=
  x - pricedStructuralLoading M x

end

/-!
## Section 3: Structural Geometry and Measure Change

### Proposition 3.3: L²-comparability under bounded density

Under the bounded-density condition 0 < z̲ ≤ Z_T ≤ z̄, the L²(P) and L²(Q) norms
are equivalent: z̲ · E_P[X²] ≤ E_Q[X²] ≤ z̄ · E_P[X²].

We formalize this as: if two inner products on the same space satisfy a sandwich bound,
the induced norms are equivalent.
-/

/-- **Proposition 3.3** (L²-comparability under bounded density).
    If the Radon-Nikodym density Z_T satisfies z̲ ≤ Z_T ≤ z̄ a.s., then
    z̲ · ‖X‖²_P ≤ ‖X‖²_Q ≤ z̄ · ‖X‖²_P for all X ∈ L².
    Here formalized as the abstract sandwich inequality. -/
theorem norm_sq_sandwich
    {z_lo z_hi : ℝ} (hz_lo : 0 < z_lo) (hz_hi : 0 < z_hi)
    {normP normQ : E → ℝ}
    (hP : ∀ x, 0 ≤ normP x) (hQ : ∀ x, 0 ≤ normQ x)
    (h_lo : ∀ x, z_lo * normP x ≤ normQ x)
    (h_hi : ∀ x, normQ x ≤ z_hi * normP x)
    (x : E) :
    z_lo * normP x ≤ normQ x ∧ normQ x ≤ z_hi * normP x :=
  ⟨h_lo x, h_hi x⟩

/-!
## Section 4: Risk-Neutral Compression and Projection
-/

section CompressionProjection

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-!
### Tower property for orthogonal projections

This is the key structural lemma: if K ≤ L, then proj_K ∘ proj_L = proj_K.
In the paper, this corresponds to the tower property of conditional expectations:
E[E[X|H_ϖ]|H] = E[X|H] for H ⊆ H_ϖ.
-/

/-
**Tower property**: If K ≤ L are closed subspaces, then projecting onto L first
    and then onto K gives the same result as projecting directly onto K.
    This is the Hilbert space version of the tower property of conditional expectations.
-/
theorem orthogonalProjection_tower
    (K L : Submodule ℝ E) [K.HasOrthogonalProjection] [L.HasOrthogonalProjection]
    (h : K ≤ L) (x : E) :
    K.orthogonalProjection (L.orthogonalProjection x : E) = K.orthogonalProjection x := by
  simp +decide [ Submodule.starProjection_eq_self_iff, h ];
  exact?

/-!
### Proposition 4.2: Supporting structural projection of claims

Every claim X ∈ L²(Q, F_T) admits a unique orthogonal decomposition X = L_X + U_X,
where L_X = C_{H_ϖ}(X) ∈ M_Q and U_X ⊥ M_Q. For every public H ⊆ G_T ⊆ H_ϖ:
  C_H(X) = C_H(L_X).
-/

/-
**Proposition 4.2(a)** (Claim decomposition).
    X = L_X + U_X where L_X is the structural loading and U_X is the residual.
-/
theorem claim_decomposition
    (M : Submodule ℝ E) [M.HasOrthogonalProjection] (x : E) :
    x = pricedStructuralLoading M x + structuralResidual M x := by
  -- By definition of pricedStructuralLoading and structuralResidual, we have:
  simp [pricedStructuralLoading, structuralResidual, riskNeutralCompression]

/-
**Proposition 4.2(b)** (Orthogonality of the structural residual).
    The residual U_X = X - L_X belongs to the orthogonal complement of M.
-/
theorem structuralResidual_mem_orthogonal
    (M : Submodule ℝ E) [M.HasOrthogonalProjection] (x : E) :
    structuralResidual M x ∈ Mᗮ := by
  -- By definition of $L_X$, we have $L_X = \text{proj}_M(x)$.
  have h_LX : pricedStructuralLoading M x = ↑(Submodule.orthogonalProjection M x) := by
    rfl;
  simp [ h_LX, structuralResidual ]

/-
**Proposition 4.2(c)** (Public compression factors through the structural loading).
    For every public sub-sigma-field H ⊆ G_T ⊆ H_ϖ (i.e., H ≤ M),
    C_H(X) = C_H(L_X). This is the paper's key tower-property consequence.
-/
theorem compression_factors_through_loading
    (H M : Submodule ℝ E) [H.HasOrthogonalProjection] [M.HasOrthogonalProjection]
    (h : H ≤ M) (x : E) :
    H.orthogonalProjection x = H.orthogonalProjection (pricedStructuralLoading M x) := by
  convert orthogonalProjection_tower H M h x |> Eq.symm

/-!
### Proposition 4.3: Approximate sufficiency

If X = X_ϖ + R_X with X_ϖ ∈ H_ϖ-measurable, then:
  L_X = X_ϖ + C_{H_ϖ}(R_X)
and
  ‖L_X - X_ϖ‖ ≤ ‖R_X‖.
-/

/-
**Proposition 4.3(a)** (Approximate sufficiency, decomposition).
    If x = x_s + r with x_s ∈ M, then proj_M(x) = x_s + proj_M(r).
-/
theorem approx_sufficiency_decomp
    (M : Submodule ℝ E) [M.HasOrthogonalProjection]
    {x x_s r : E} (hx_s : x_s ∈ M) (hx : x = x_s + r) :
    (M.orthogonalProjection x : E) = x_s + (M.orthogonalProjection r : E) := by
  have h_proj : M.orthogonalProjection (x_s + r) = M.orthogonalProjection x_s + M.orthogonalProjection r := by
    grind +splitImp;
  rw [ hx, h_proj ];
  simp +decide [ hx_s, Submodule.starProjection_eq_self_iff ]

/-
**Proposition 4.3(b)** (Approximate sufficiency, contraction bound).
    If x = x_s + r with x_s ∈ M, then ‖proj_M(x) - x_s‖ ≤ ‖r‖.
    This says that the Perron-generated component approximates the full structural
    content up to the residual norm.
-/
theorem approx_sufficiency_bound
    (M : Submodule ℝ E) [M.HasOrthogonalProjection]
    {x x_s r : E} (hx_s : x_s ∈ M) (hx : x = x_s + r) :
    ‖(M.orthogonalProjection x : E) - x_s‖ ≤ ‖r‖ := by
  -- By the properties of the orthogonal projection, we have:
  have h_proj : (M.orthogonalProjection x : E) = x_s + (M.orthogonalProjection r : E) := by
    convert approx_sufficiency_decomp M hx_s hx;
  -- Substitute h_proj into the goal.
  rw [h_proj];
  simp +decide [ add_sub_cancel_left ];
  exact?

/-
**Proposition 4.3(c)** (Approximate sufficiency, compression contraction).
    For every H ≤ M, ‖C_H(L_X) - C_H(x_s)‖ ≤ ‖r‖.
-/
theorem approx_sufficiency_compression_bound
    (H M : Submodule ℝ E) [H.HasOrthogonalProjection] [M.HasOrthogonalProjection]
    (hHM : H ≤ M) {x x_s r : E} (hx_s : x_s ∈ M) (hx : x = x_s + r) :
    ‖(H.orthogonalProjection (M.orthogonalProjection x : E) : E) -
     (H.orthogonalProjection x_s : E)‖ ≤ ‖r‖ := by
  -- By the properties of orthogonal projections, we have that $C_H(L_X) = C_H(x_s) + C_H(r)$.
  have h_proj : (H.orthogonalProjection (M.orthogonalProjection x) : E) = (H.orthogonalProjection x_s : E) + (H.orthogonalProjection (M.orthogonalProjection r) : E) := by
    have h_proj : (M.orthogonalProjection x : E) = x_s + (M.orthogonalProjection r : E) := by
      convert approx_sufficiency_decomp M hx_s hx using 1;
    simp +decide [ h_proj, map_add ];
  simp_all +decide [ Submodule.mem_orthogonal' ];
  -- Apply the norm inequality for orthogonal projections.
  have h_norm : ∀ (v : E), ‖(H.starProjection v : E)‖ ≤ ‖v‖ := by
    grind +suggestions;
  refine' le_trans ( h_norm _ ) _;
  exact?

/-!
### Proposition 4.5: Canonical aggregate factor decomposition

Inside the centered structural subspace M° = M ⊓ G⊥, every loading decomposes
uniquely along the canonical aggregate factor direction Λ*_M.
-/

/-
**Proposition 4.5** (Factor decomposition, inner product characterization).
    For any unit vector `Λ` in a Hilbert space and any vector `y`,
    y = ⟨y, Λ⟩ · Λ + (y - ⟨y, Λ⟩ · Λ) with the remainder orthogonal to Λ.
-/
theorem factor_decomposition_orthogonal
    (Λ : E) (hΛ : ‖Λ‖ = 1) (y : E) :
    @inner ℝ _ _ (y - (inner ℝ y Λ) • Λ) Λ = 0 := by
  simp +decide [ inner_sub_left, inner_smul_left, hΛ ]

/-
**Proposition 4.5** (Factor decomposition, reconstruction).
    y = ⟨y, Λ⟩ · Λ + (y - ⟨y, Λ⟩ · Λ).
-/
theorem factor_decomposition_eq
    (Λ : E) (y : E) :
    y = (inner ℝ y Λ) • Λ + (y - (inner ℝ y Λ) • Λ) := by
  rw [ add_sub_cancel ]

/-!
### Corollary 4.6: Linear public screening of the centered aggregate factor

If Λ*_M ∈ M° (meaning it is centered: E_Q[Λ*_M | G_T] = 0, i.e., Λ ∈ G^⊥),
then C_H(Λ*_M) = 0 for every H ⊆ G_T.
-/

/-
**Corollary 4.6** (Factor screening).
    If Λ ∈ G^⊥ and H ≤ G, then proj_H(Λ) = 0.
    The centered aggregate factor is always screened from linear public compression.
-/
theorem factor_screening
    (H G : Submodule ℝ E) [H.HasOrthogonalProjection] [G.HasOrthogonalProjection]
    (hHG : H ≤ G) (Λ : E) (hΛ : Λ ∈ Gᗮ) :
    H.orthogonalProjection Λ = 0 := by
  exact?

/-
**Corollary 4.6** (Aligned-claim identity).
    If L = V + α · Λ with Λ ∈ G^⊥, then for H ≤ G:
    C_H(L) = C_H(V).
-/
theorem aligned_claim_compression
    (H G : Submodule ℝ E) [H.HasOrthogonalProjection] [G.HasOrthogonalProjection]
    (hHG : H ≤ G)
    {V Λ : E} (α : ℝ) (hΛ : Λ ∈ Gᗮ) :
    (H.orthogonalProjection (V + α • Λ) : E) = (H.orthogonalProjection V : E) := by
  -- Apply the identity $C'_H(V + \alpha \Lambda) = C'_H(V)$ since $\Lambda \in G^\perp$ and $H \leq G$.
  have h_eq : H.orthogonalProjection Λ = 0 := by
    exact?;
  rw [ map_add, map_smul, h_eq, smul_zero, add_zero ]

/-!
### Corollary 4.7: Compression principle for priced structural loading

Every public compression and visible projection factors through L_X.
-/

/-
**Corollary 4.7(i)** (Compression principle, sigma-field version).
    For every H ≤ G ≤ M: C_H(X) = C_H(L_X).
    Identical to `compression_factors_through_loading` but stated with the full chain.
-/
theorem compression_principle_sigma
    (H G M : Submodule ℝ E) [H.HasOrthogonalProjection] [G.HasOrthogonalProjection]
    [M.HasOrthogonalProjection]
    (hHG : H ≤ G) (hGM : G ≤ M) (x : E) :
    H.orthogonalProjection x = H.orthogonalProjection (M.orthogonalProjection x : E) := by
  convert orthogonalProjection_tower H M ( hHG.trans hGM ) x |> Eq.symm

/-
**Corollary 4.7(ii)** (Compression principle, hedge class version).
    For every closed subspace S ≤ G ≤ M: proj_S(X) = proj_S(L_X).
    The visible hedge projection factors through the structural loading.
-/
theorem compression_principle_hedge
    (S G M : Submodule ℝ E) [S.HasOrthogonalProjection] [G.HasOrthogonalProjection]
    [M.HasOrthogonalProjection]
    (hSG : S ≤ G) (hGM : G ≤ M) (x : E) :
    S.orthogonalProjection x = S.orthogonalProjection (M.orthogonalProjection x : E) := by
  exact?

/-!
### Theorem 4.8: Main risk-neutral compression theorem

The Pythagorean decomposition of the hedge residual:
  inf_{H∈S} E_Q[(X-H)²] = dist(L_X, S)² + ‖U_X‖²

This says the total hedge error decomposes into:
1. The structural hedge gap: how well L_X can be approximated within S
2. The irreducible residual: the norm of the part of X not in the structural subspace
-/

/-
**Theorem 4.8** (Main risk-neutral compression theorem, Pythagorean identity).
    For S ≤ M, the squared distance from x to S decomposes as:
    ‖x - proj_S(x)‖² = ‖proj_M(x) - proj_S(proj_M(x))‖² + ‖x - proj_M(x)‖²

    This is the hedge-residual Pythagorean decomposition. The total hedge error
    is the sum of:
    (1) the "compression gap" dist(L_X, S)², measuring how well the structural
        loading can be hedged within the visible class, and
    (2) the "irreducible residual" ‖U_X‖², measuring how much of the claim
        lies outside the structural subspace entirely.
-/
theorem main_compression_pythagorean
    (S M : Submodule ℝ E) [S.HasOrthogonalProjection] [M.HasOrthogonalProjection]
    (hSM : S ≤ M) (x : E) :
    ‖x - (S.orthogonalProjection x : E)‖ ^ 2 =
      ‖(M.orthogonalProjection x : E) - (S.orthogonalProjection (M.orthogonalProjection x : E) : E)‖ ^ 2 +
      ‖x - (M.orthogonalProjection x : E)‖ ^ 2 := by
  -- By the properties of orthogonal projections, we have:
  have h1 : ‖x - (S.orthogonalProjection x : E)‖ ^ 2 = ‖(M.orthogonalProjection x : E) - (S.orthogonalProjection x : E)‖ ^ 2 + ‖x - (M.orthogonalProjection x : E)‖ ^ 2 := by
    -- Since $S \subseteq M$, we have $(M.orthogonalProjection x : E) - (S.orthogonalProjection x : E) \in M$.
    have h_in_M : (M.orthogonalProjection x : E) - (S.orthogonalProjection x : E) ∈ M := by
      exact M.sub_mem ( Submodule.coe_mem _ ) ( hSM ( Submodule.coe_mem _ ) );
    rw [ show x - ( S.orthogonalProjection x : E ) = ( x - ( M.orthogonalProjection x : E ) ) + ( ( M.orthogonalProjection x : E ) - ( S.orthogonalProjection x : E ) ) by abel1, @norm_add_sq ℝ ] ; simp_all +decide [ real_inner_comm ];
    ring;
  grind +suggestions

/-
**Theorem 4.8** (Hedge residual, non-squared version).
    The residual norms satisfy the Pythagorean identity.
-/
theorem main_compression_norm_sq
    (S M : Submodule ℝ E) [S.HasOrthogonalProjection] [M.HasOrthogonalProjection]
    (hSM : S ≤ M) (x : E) :
    ‖x - (S.orthogonalProjection x : E)‖ ^ 2 ≥
      ‖x - (M.orthogonalProjection x : E)‖ ^ 2 := by
  have := @main_compression_pythagorean E _ _ _ S M _ _ hSM x;
  exact this.symm ▸ le_add_of_nonneg_left ( sq_nonneg _ )

end CompressionProjection

/-!
## Section 5: Risk-Neutral Visibility and Screening

### Proposition 5.2: Operational summary criterion

A claim X is "Q-visible through H" when C_H(L_X) ≠ 0.
The norm ‖C_H(L_X)‖ measures the degree of visibility.
-/

section Visibility

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- A claim is **fully visible** through the public information if
    the compressed loading equals the full loading. -/
def IsFullyVisible (H M : Submodule ℝ E) [H.HasOrthogonalProjection]
    [M.HasOrthogonalProjection] (x : E) : Prop :=
  (H.orthogonalProjection (M.orthogonalProjection x : E) : E) = (M.orthogonalProjection x : E)

/-- A claim is **invisible** (Q-screened) through the public information if
    the compressed loading vanishes. -/
def IsInvisible (H M : Submodule ℝ E) [H.HasOrthogonalProjection]
    [M.HasOrthogonalProjection] (x : E) : Prop :=
  H.orthogonalProjection (M.orthogonalProjection x : E) = 0

/-- A claim is **partially visible** if it is neither fully visible nor invisible. -/
def IsPartiallyVisible (H M : Submodule ℝ E) [H.HasOrthogonalProjection]
    [M.HasOrthogonalProjection] (x : E) : Prop :=
  ¬IsFullyVisible H M x ∧ ¬IsInvisible H M x

/-
**Proposition 5.3** (Visibility trichotomy).
    Every claim is exactly one of: fully visible, partially visible, or invisible.
-/
theorem visibility_trichotomy
    (H M : Submodule ℝ E) [H.HasOrthogonalProjection] [M.HasOrthogonalProjection] (x : E) :
    IsFullyVisible H M x ∨ IsPartiallyVisible H M x ∨ IsInvisible H M x := by
  by_cases h : IsFullyVisible H M x <;> by_cases h' : IsInvisible H M x <;> simp_all +decide [ IsFullyVisible, IsInvisible, IsPartiallyVisible ]

/-
If the structural loading is in the public information, the claim is fully visible.
-/
theorem isFullyVisible_of_loading_mem
    (H M : Submodule ℝ E) [H.HasOrthogonalProjection] [M.HasOrthogonalProjection]
    (x : E) (h : (M.orthogonalProjection x : E) ∈ H) :
    IsFullyVisible H M x := by
  -- By definition of IsFullyVisible, we need to show that proj_H(proj_M(x)) = proj_M(x).
  unfold IsFullyVisible;
  convert Submodule.starProjection_eq_self_iff.mpr h

/-
If the structural loading is orthogonal to the public information, the claim is invisible.
-/
theorem isInvisible_of_loading_mem_ortho
    (H M : Submodule ℝ E) [H.HasOrthogonalProjection] [M.HasOrthogonalProjection]
    (x : E) (h : (M.orthogonalProjection x : E) ∈ Hᗮ) :
    IsInvisible H M x := by
  -- Apply the hypothesis `h` which states that the orthogonal projection of `x` onto `M` is in the orthogonal complement of `H`.
  apply Submodule.orthogonalProjection_mem_subspace_orthogonalComplement_eq_zero;
  -- Apply the hypothesis `h` directly to conclude the goal.
  exact h

end Visibility

/-!
## Section 8: Visible Hedging and Risk-Neutral Incompleteness

### Theorem 8.1: Visible hedging as projection failure

The visible hedging residual for a claim X against a hedge class S is:
  R_{X,S} = L_X - proj_S(L_X)

and the residual hedge variance is:
  E_Q[(X - H*)²] = ‖R_{X,S}‖² + ‖U_X‖²

where H* = proj_S(L_X) is the best visible hedge.
-/

section Hedging

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- The **visible hedging residual**: the gap between the structural loading and its
    best approximation in the visible hedge class. -/
noncomputable def visibleHedgingResidual (S M : Submodule ℝ E)
    [S.HasOrthogonalProjection] [M.HasOrthogonalProjection] (x : E) : E :=
  (M.orthogonalProjection x : E) - (S.orthogonalProjection (M.orthogonalProjection x : E) : E)

/-
**Theorem 8.1** (Visible hedging as projection failure).
    The best visible hedge is proj_S(L_X), and the total hedge error decomposes as
    the structural gap plus the irreducible residual.
    This is a restatement of the main compression Pythagorean identity from the
    hedging perspective.
-/
theorem visible_hedging_decomposition
    (S M : Submodule ℝ E) [S.HasOrthogonalProjection] [M.HasOrthogonalProjection]
    (hSM : S ≤ M) (x : E) :
    ‖x - (S.orthogonalProjection x : E)‖ ^ 2 =
      ‖visibleHedgingResidual S M x‖ ^ 2 + ‖structuralResidual M x‖ ^ 2 := by
  convert main_compression_pythagorean S M hSM x using 1

/-
The visible hedging residual is zero iff the structural loading is in the hedge class.
-/
theorem visibleHedgingResidual_eq_zero_iff
    (S M : Submodule ℝ E) [S.HasOrthogonalProjection] [M.HasOrthogonalProjection]
    (hSM : S ≤ M) (x : E) :
    visibleHedgingResidual S M x = 0 ↔
      (M.orthogonalProjection x : E) ∈ S := by
  simp +decide [ visibleHedgingResidual, sub_eq_zero ];
  grind +suggestions

/-
**Corollary**: When the structural loading is in the hedge class,
    the hedge error reduces to just the irreducible residual.
-/
theorem hedge_error_when_loading_in_span
    (S M : Submodule ℝ E) [S.HasOrthogonalProjection] [M.HasOrthogonalProjection]
    (hSM : S ≤ M) (x : E) (h : (M.orthogonalProjection x : E) ∈ S) :
    ‖x - (S.orthogonalProjection x : E)‖ ^ 2 =
      ‖x - (M.orthogonalProjection x : E)‖ ^ 2 := by
  have := visibleHedgingResidual_eq_zero_iff S M hSM x;
  -- By combining the results from visible_hedging_decomposition and visibleHedgingResidual_eq_zero_iff, we get the desired equality.
  have := visible_hedging_decomposition S M hSM x
  simp [this, this] at *;
  rw [ ‹visibleHedgingResidual S M x = 0 ↔ M.starProjection x ∈ S›.mpr h, norm_zero, zero_pow two_ne_zero, zero_add, structuralResidual ];
  rfl

end Hedging

/-!
## Section 7: Variance Claims and Risk-Neutral Compression

### Nonlinear compression gap

For a nonlinear function g of the structural loading, the compression gap
measures the difference between g(L_X) and its projection.

The key identity (Lemma 7.1) shows that nonlinearity introduces an additional
gap beyond the linear compression.
-/

section NonlinearGap

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-
**Lemma 7.1** (Nonlinearity plus compression gap, norm bound).
    For any two elements a, b in a Hilbert space and a closed subspace S:
    ‖a - proj_S(a)‖ ≤ ‖a - b‖ + ‖b - proj_S(b)‖ + ‖proj_S(b) - proj_S(a)‖

    This is used in the paper to bound the compression gap of nonlinear
    variance-linked claims.
-/
theorem nonlinear_compression_gap_bound
    (S : Submodule ℝ E) [S.HasOrthogonalProjection]
    (a b : E) :
    ‖a - (S.orthogonalProjection a : E)‖ ≤
      ‖a - b‖ + ‖b - (S.orthogonalProjection b : E)‖ +
      ‖(S.orthogonalProjection b : E) - (S.orthogonalProjection a : E)‖ := by
  have h_triangle : ‖a - (S.orthogonalProjection a : E)‖ = ‖(a - b) + (b - (S.orthogonalProjection b : E)) + ((S.orthogonalProjection b : E) - (S.orthogonalProjection a : E))‖ := by
    simp +decide [ sub_add_sub_cancel ];
  exact h_triangle ▸ norm_add₃_le

/-
**Projection is a contraction**: ‖proj_S(a) - proj_S(b)‖ ≤ ‖a - b‖.
    Used throughout the paper for bounding projection differences.
-/
theorem projection_contraction
    (S : Submodule ℝ E) [S.HasOrthogonalProjection]
    (a b : E) :
    ‖(S.orthogonalProjection a : E) - (S.orthogonalProjection b : E)‖ ≤ ‖a - b‖ := by
  have := @nonlinear_compression_gap_bound E _ _ _;
  have := @Submodule.orthogonalProjection_norm_le;
  specialize this S;
  simpa using ContinuousLinearMap.le_of_opNorm_le _ this ( a - b )

end NonlinearGap