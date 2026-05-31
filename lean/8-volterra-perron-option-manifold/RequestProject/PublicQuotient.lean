/-
  ## Public-Observable Quotient and Non-Identification

  Formalization of key results from Section 5 ("Public non-identification") of

    J. Vidal Llauradó, "Volterra–Perron Pricing of the Option Manifold" (2026).

  ### Theorem 5.2 (Maximality of the public-observable quotient)
  Let Z : X → Z be any state functional. The following are equivalent:
    1. Z is identified by the public option manifold (factors through P).
    2. Z is constant on public-indistinguishability classes.
    3. Z factors through the quotient X^pub.
-/

import Mathlib

set_option maxHeartbeats 800000

/-! ### Definition 5.1: Public indistinguishability as a setoid -/

/-- The public-indistinguishability relation induced by a pricing map `P`.
  Two states are public-indistinguishable iff they have the same public prices. -/
def publicIndistinguishable {X Y : Type*} (P : X → Y) : X → X → Prop :=
  fun θ θ' => P θ = P θ'

theorem publicIndistinguishable_equivalence {X Y : Type*} (P : X → Y) :
    Equivalence (publicIndistinguishable P) :=
  ⟨fun _ => rfl, fun h => h.symm, fun h1 h2 => h1.trans h2⟩

/-- The setoid of public indistinguishability. -/
def publicSetoid {X Y : Type*} (P : X → Y) : Setoid X :=
  ⟨publicIndistinguishable P, publicIndistinguishable_equivalence P⟩

/-! ### Theorem 5.2: Maximality of the public-observable quotient -/

/-- **Theorem 5.2, direction (1) ⟹ (2):**
  If `Z = ζ ∘ P` for some `ζ`, then `Z` is constant on fibers of `P`. -/
theorem public_quotient_1_implies_2 {X Y Z : Type*}
    (P : X → Y) (Zfun : X → Z) (ζ : Y → Z)
    (hfactor : Zfun = ζ ∘ P) :
    ∀ θ θ' : X, publicIndistinguishable P θ θ' → Zfun θ = Zfun θ' := by
  simp [hfactor]
  intros θ θ' h_eq
  apply congr_arg ζ h_eq

/-- **Theorem 5.2, direction (2) ⟹ (3):**
  If `Z` is constant on public-indistinguishability classes, then it factors
  through the quotient `X / ∼_pub`. -/
theorem public_quotient_2_implies_3 {X Y Z : Type*}
    (P : X → Y) (Zfun : X → Z)
    (hconst : ∀ θ θ' : X, publicIndistinguishable P θ θ' → Zfun θ = Zfun θ') :
    ∃ Zbar : Quotient (publicSetoid P) → Z,
      Zfun = Zbar ∘ Quotient.mk (publicSetoid P) := by
  exact ⟨Quotient.lift Zfun hconst, rfl⟩

/-
**Theorem 5.2, direction (3) ⟹ (1):**
  If `Z` is constant on fibers of `P`, then it factors through the
  restricted map on the range of `P`.
-/
theorem public_quotient_3_implies_1 {X Y Z : Type*}
    (P : X → Y) (Zfun : X → Z)
    (hconst : ∀ θ θ' : X, publicIndistinguishable P θ θ' → Zfun θ = Zfun θ') :
    ∃ ζ : Set.range P → Z, ∀ x : X, Zfun x = ζ ⟨P x, Set.mem_range_self x⟩ := by
  use fun ⟨y, hy⟩ => Zfun (Classical.choose hy);
  exact fun x => hconst _ _ ( Eq.symm ( Classical.choose_spec ( Set.mem_range_self x ) ) )

/-
**Theorem 5.2 (combined):** `Z` is identified by the public manifold iff
  it is constant on public-indistinguishability classes iff it factors through `P`
  (on the range).
-/
theorem public_quotient_maximality {X Y Z : Type*}
    (P : X → Y) (Zfun : X → Z) :
    (∀ θ θ' : X, publicIndistinguishable P θ θ' → Zfun θ = Zfun θ') ↔
    (∃ ζ : Set.range P → Z, ∀ x : X, Zfun x = ζ ⟨P x, Set.mem_range_self x⟩) := by
  constructor <;> intro h;
  · exact?;
  · grind +locals

/-! ### Theorem 5.5 (Public completion and residual collapse)

  Abstracted: a loading L has zero residual relative to a closed subspace S
  iff every element of S⊥ is orthogonal to L.
-/

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-
**Theorem 5.5 (abstract form):** For a closed subspace `S`,
  `L ∈ S` iff every `R ∈ Sᗮ` is orthogonal to `L`.
-/
theorem mem_submodule_iff_orthogonal_complement
    (S : Submodule ℝ H) (hclosed : IsClosed (S : Set H)) (L : H) :
    L ∈ S ↔ (∀ R : H, R ∈ Sᗮ → @inner ℝ H _ R L = 0) := by
  refine' ⟨ fun hL R hR => _, fun hL => _ ⟩;
  · exact?;
  · convert Submodule.mem_orthogonal' _ _ |>.2 fun R hR => ?_;
    rotate_left;
    exact Sᗮ;
    · rw [ real_inner_comm, hL R hR ];
    · rw [ Submodule.orthogonal_orthogonal_eq_closure ];
      grind +suggestions

/-
**Corollary 5.6 (Selector redundancy at public completion):**
  If `L ∈ S`, then the projection of `L` onto `Sᗮ` is zero.
-/
theorem selector_redundancy_at_completion
    (S : Submodule ℝ H) (L : H) (hL : L ∈ S)
    [Submodule.HasOrthogonalProjection Sᗮ] :
    Submodule.orthogonalProjection Sᗮ L = 0 := by
  exact?