import Mathlib

/-!
# MATH-518: an axiomatic homology theory

Mathlib (at the pinned revision) defines singular homology but proves neither exactness nor
excision for it, so we work with an *axiomatic* homology theory: a structure `HomologyTheory`
whose fields are the Eilenberg–Steenrod axioms that the proofs of MATH-518 use.  Singular
homology with integer coefficients satisfies every field (Hatcher, *Algebraic Topology*, §2.1–2.3);
this is NOT proved here.

Conventions.
* Spaces are `X : Type` with `[TopologicalSpace X]`; a pair is `(X, A)` with `A : Set X`.
  A subspace `A ⊆ X` is the subtype `↥A`; a subset `B` of `X` seen inside `↥A` is
  `Subtype.val ⁻¹' B` (that is, `A ∩ B`).
* `H n X A` is the relative group `H_n(X, A)`, `n : ℤ`; `H_n(X) = H n X ∅`.
* Reduced homology of a pointed space is modelled as `H̃_n(X) = H_n(X, {x₀})` (for singular
  homology the two are naturally isomorphic, Hatcher Prop. 2.22 / p. 118).

Axioms (fields):
* `map`, `map_id`, `map_comp` — functoriality on maps of pairs;
* `homotopy` — homotopy invariance for homotopies through maps of pairs;
* `bd`, `exact_left`, `exact_mid`, `exact_right` — the long exact sequence of a triple
  `B ⊆ A ⊆ X` (the pair sequence is the case `B = ∅`);
* `excision` — if `Z ⊆ A ⊆ X` and `closure Z ⊆ interior A`, then `(X ∖ Z, A ∖ Z) ↪ (X, A)`
  induces isomorphisms.

The computations of a point and of spheres are *not* fields: they are the separate hypotheses
`PointAxiom` and `SphereAxiom`, used only in part (b).  Naturality of `bd`, additivity and
Mayer–Vietoris are not assumed (Mayer–Vietoris for the case needed is derived in `Wedge.lean`).
`HomologyTheory.trivial` shows the fields alone are satisfiable (by the zero theory).
-/

open Set Topology
open scoped unitInterval

noncomputable section

namespace LeanMisc.MATH518

/-- The inclusion of a subspace, as a continuous map. -/
def incl {X : Type} [TopologicalSpace X] (A : Set X) : C(A, X) :=
  ⟨Subtype.val, continuous_subtype_val⟩

/-- An (unreduced, relative, `ℤ`-graded) homology theory on pairs of spaces, given by the
Eilenberg–Steenrod axioms used in MATH-518 (dimension/sphere computations are separate). -/
structure HomologyTheory where
  /-- `H n X A` is `H_n(X, A)`. -/
  H : ℤ → (X : Type) → [TopologicalSpace X] → Set X → Type
  /-- Each `H_n(X, A)` is an abelian group. -/
  grp : ∀ (n : ℤ) (X : Type) [TopologicalSpace X] (A : Set X), AddCommGroup (H n X A)
  /-- A map of pairs `f : (X, A) → (Y, B)` induces `f_* : H_n(X, A) → H_n(Y, B)`. -/
  map : ∀ (n : ℤ) {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] {A : Set X} {B : Set Y}
    (f : C(X, Y)), MapsTo f A B → H n X A →+ H n Y B
  /-- `id_* = id`. -/
  map_id : ∀ (n : ℤ) {X : Type} [TopologicalSpace X] {A : Set X} (hA : MapsTo id A A),
    map n (ContinuousMap.id X) hA = AddMonoidHom.id (H n X A)
  /-- `(g ∘ f)_* = g_* ∘ f_*`. -/
  map_comp : ∀ (n : ℤ) {X Y Z : Type} [TopologicalSpace X] [TopologicalSpace Y]
    [TopologicalSpace Z] {A : Set X} {B : Set Y} {C : Set Z} (g : C(Y, Z)) (f : C(X, Y))
    (hg : MapsTo g B C) (hf : MapsTo f A B) (hgf : MapsTo (g.comp f) A C),
    map n (g.comp f) hgf = (map n g hg).comp (map n f hf)
  /-- Homotopy invariance: maps of pairs homotopic through maps of pairs induce the same map. -/
  homotopy : ∀ (n : ℤ) {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] {A : Set X}
    {B : Set Y} (f g : C(X, Y)) (hf : MapsTo f A B) (hg : MapsTo g A B) (F : f.Homotopy g),
    (∀ t : I, MapsTo (fun x => F (t, x)) A B) → map n f hf = map n g hg
  /-- The boundary map `∂ : H_n(X, A) → H_{n-1}(A, B)` of a triple `(X, A, B)`. -/
  bd : ∀ (n : ℤ) {X : Type} [TopologicalSpace X] (A B : Set X),
    H n X A →+ H (n - 1) A (Subtype.val ⁻¹' B)
  /-- Exactness of `H_n(A, B) → H_n(X, B) → H_n(X, A)` for `B ⊆ A ⊆ X`. -/
  exact_left : ∀ (n : ℤ) {X : Type} [TopologicalSpace X] {A B : Set X} (hBA : B ⊆ A),
    Function.Exact (map n (A := Subtype.val ⁻¹' B) (B := B) (incl A) fun _ hx => hx)
      (map n (A := B) (B := A) (ContinuousMap.id X) fun _ hx => hBA hx)
  /-- Exactness of `H_n(X, B) → H_n(X, A) → H_{n-1}(A, B)` for `B ⊆ A ⊆ X`. -/
  exact_mid : ∀ (n : ℤ) {X : Type} [TopologicalSpace X] {A B : Set X} (hBA : B ⊆ A),
    Function.Exact (map n (A := B) (B := A) (ContinuousMap.id X) fun _ hx => hBA hx) (bd n A B)
  /-- Exactness of `H_n(X, A) → H_{n-1}(A, B) → H_{n-1}(X, B)` for `B ⊆ A ⊆ X`. -/
  exact_right : ∀ (n : ℤ) {X : Type} [TopologicalSpace X] {A B : Set X} (_hBA : B ⊆ A),
    Function.Exact (bd n A B)
      (map (n - 1) (A := Subtype.val ⁻¹' B) (B := B) (incl A) fun _ hx => hx)
  /-- Excision: if `Z ⊆ A ⊆ X` and `closure Z ⊆ interior A`, the inclusion
  `(X ∖ Z, A ∖ Z) → (X, A)` induces isomorphisms. -/
  excision : ∀ (n : ℤ) {X : Type} [TopologicalSpace X] {Z A : Set X}, Z ⊆ A →
    closure Z ⊆ interior A →
    Function.Bijective (map n (A := Subtype.val ⁻¹' A) (B := A) (incl Zᶜ) fun _ hx => hx)

attribute [instance] HomologyTheory.grp

namespace HomologyTheory

/-- Dimension axiom: `H_k(pt) ≅ ℤ` for `k = 0` and `H_k(pt) = 0` for `k ≠ 0`. -/
def PointAxiom (h : HomologyTheory) : Prop :=
  ∀ k : ℤ, (k = 0 → Nonempty (h.H k Unit ∅ ≃+ ℤ)) ∧ (k ≠ 0 → Subsingleton (h.H k Unit ∅))

/-- The base point `e₀ = (1, 0, …, 0)` of the unit sphere `S^m ⊆ ℝ^{m+1}`. -/
def spherePt (m : ℕ) : Metric.sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1 :=
  ⟨EuclideanSpace.single 0 1, by simp⟩

/-- Homology of spheres: `H̃_k(S^m) = H_k(S^m, e₀) ≅ ℤ` for `k = m` and `= 0` for `k ≠ m`,
for every `m ≥ 0` (`S^m` is the unit sphere of `ℝ^{m+1}`; `S^0 = {±1}`). -/
def SphereAxiom (h : HomologyTheory) : Prop :=
  ∀ (m : ℕ) (k : ℤ),
    (k = m → Nonempty
      (h.H k (Metric.sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1) {spherePt m} ≃+ ℤ)) ∧
    (k ≠ m → Subsingleton
      (h.H k (Metric.sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1) {spherePt m}))

/-- Sanity check: the zero theory satisfies all fields of `HomologyTheory` (it fails
`PointAxiom`), so the fields are not contradictory. -/
def trivial : HomologyTheory where
  H _ _ _ _ := PUnit
  grp _ _ _ _ := inferInstance
  map _ _ _ _ _ _ _ _ _ := 0
  map_id _ _ _ _ _ := Subsingleton.elim _ _
  map_comp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ := Subsingleton.elim _ _
  homotopy _ _ _ _ _ _ _ _ _ _ _ _ _ := rfl
  bd _ _ _ _ _ := 0
  exact_left _ _ _ _ _ _ _ := ⟨fun _ => ⟨PUnit.unit, Subsingleton.elim _ _⟩,
    fun _ => Subsingleton.elim _ _⟩
  exact_mid _ _ _ _ _ _ _ := ⟨fun _ => ⟨PUnit.unit, Subsingleton.elim _ _⟩,
    fun _ => Subsingleton.elim _ _⟩
  exact_right _ _ _ _ _ _ _ := ⟨fun _ => ⟨PUnit.unit, Subsingleton.elim _ _⟩,
    fun _ => Subsingleton.elim _ _⟩
  excision _ _ _ _ _ _ _ := ⟨fun _ _ _ => Subsingleton.elim _ _,
    fun _ => ⟨PUnit.unit, Subsingleton.elim _ _⟩⟩

variable (h : HomologyTheory)

section General

variable {X Y Z : Type} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]

theorem map_comp_apply (n : ℤ) {A : Set X} {B : Set Y} {C : Set Z} (g : C(Y, Z)) (f : C(X, Y))
    (k : C(X, Z)) (hg : MapsTo g B C) (hf : MapsTo f A B) (hk : MapsTo k A C)
    (e : g.comp f = k) (a : h.H n X A) :
    h.map n k hk a = h.map n g hg (h.map n f hf a) := by
  subst e
  exact DFunLike.congr_fun (h.map_comp n g f hg hf hk) a

theorem map_id_apply (n : ℤ) {A : Set X} (k : C(X, X)) (hk : MapsTo k A A)
    (e : k = ContinuousMap.id X) (a : h.H n X A) : h.map n k hk a = a := by
  subst e
  exact DFunLike.congr_fun (h.map_id n hk) a

theorem map_map_eq_self (n : ℤ) {A : Set X} {B : Set Y} (f : C(X, Y)) (g : C(Y, X))
    (hf : MapsTo f A B) (hg : MapsTo g B A) (e : g.comp f = ContinuousMap.id X)
    (a : h.H n X A) : h.map n g hg (h.map n f hf a) = a := by
  rw [← h.map_comp_apply n g f (g.comp f) hg hf (hg.comp hf) rfl a]
  exact h.map_id_apply n _ _ e a

theorem bijective_of_inverse (n : ℤ) {A : Set X} {B : Set Y} (f : C(X, Y)) (g : C(Y, X))
    (hf : MapsTo f A B) (hg : MapsTo g B A)
    (hgf : ∀ a, h.map n g hg (h.map n f hf a) = a)
    (hfg : ∀ b, h.map n f hf (h.map n g hg b) = b) :
    Function.Bijective (h.map n f hf) :=
  ⟨Function.LeftInverse.injective hgf, Function.RightInverse.surjective hfg⟩

/-- A homeomorphism of pairs induces isomorphisms. -/
theorem bijective_of_homeomorph (n : ℤ) {A : Set X} {B : Set Y} (φ : X ≃ₜ Y)
    (hA : MapsTo φ A B) (hB : MapsTo φ.symm B A) :
    Function.Bijective (h.map n (φ : C(X, Y)) hA) :=
  h.bijective_of_inverse n _ (φ.symm : C(Y, X)) hA hB
    (h.map_map_eq_self n _ _ hA hB (ContinuousMap.ext fun x => φ.symm_apply_apply x))
    (h.map_map_eq_self n _ _ hB hA (ContinuousMap.ext fun y => φ.apply_symm_apply y))

/-- If `g ∘ f = id` and `f ∘ g ≃ id` through maps of pairs, then `f_*` is bijective. -/
theorem bijective_of_retract (n : ℤ) {A : Set X} {B : Set Y} (f : C(X, Y)) (g : C(Y, X))
    (hf : MapsTo f A B) (hg : MapsTo g B A) (hgf : g.comp f = ContinuousMap.id X)
    (G : (ContinuousMap.id Y).Homotopy (f.comp g)) (hG : ∀ t : I, MapsTo (fun y => G (t, y)) B B) :
    Function.Bijective (h.map n f hf) := by
  refine h.bijective_of_inverse n f g hf hg (h.map_map_eq_self n f g hf hg hgf) fun b => ?_
  rw [← h.map_comp_apply n f g (f.comp g) hf hg (hf.comp hg) rfl b,
    ← h.homotopy n (ContinuousMap.id Y) (f.comp g) (fun _ hy => hy) (hf.comp hg) G hG]
  exact h.map_id_apply n _ _ rfl b

theorem nontrivial_congr {G G' : Type} [AddCommGroup G] [AddCommGroup G'] {f : G →+ G'}
    (hf : Function.Bijective f) : Nontrivial G ↔ Nontrivial G' :=
  ⟨fun _ => (Equiv.ofBijective f hf).symm.nontrivial, fun _ => (Equiv.ofBijective f hf).nontrivial⟩

theorem nontrivial_iff_of {G : Type} [AddCommGroup G] {k j : ℤ}
    (h1 : k = j → Nonempty (G ≃+ ℤ)) (h2 : k ≠ j → Subsingleton G) : Nontrivial G ↔ k = j := by
  constructor
  · intro hn
    by_contra hne
    exact not_nontrivial_iff_subsingleton.mpr (h2 hne) hn
  · intro hkj
    obtain ⟨e⟩ := h1 hkj
    exact e.toEquiv.nontrivial

/-- `H_n(X, X) = 0` (from the exact sequence of the triple `(X, X, ∅)`). -/
theorem subsingleton_univ (n : ℤ) : Subsingleton (h.H n X univ) := by
  have hB : (∅ : Set X) ⊆ univ := empty_subset _
  let s : C(X, (univ : Set X)) := ⟨fun x => ⟨x, mem_univ x⟩, continuous_id.subtype_mk _⟩
  have hbij : ∀ k : ℤ, Function.Bijective
      (h.map k (A := Subtype.val ⁻¹' (∅ : Set X)) (B := ∅) (incl univ) fun _ hx => hx) := by
    intro k
    exact h.bijective_of_inverse k (incl univ) s _ (fun _ hx => hx)
      (h.map_map_eq_self k _ _ _ _ (ContinuousMap.ext fun _ => rfl))
      (h.map_map_eq_self k _ _ _ _ (ContinuousMap.ext fun _ => rfl))
  have hj0 : ∀ a : h.H n X ∅, h.map n (A := ∅) (B := univ) (ContinuousMap.id X)
      (fun _ hx => hB hx) a = 0 := fun a =>
    ((h.exact_left n hB) a).2 ((hbij n).2 a)
  have hall : ∀ y : h.H n X univ, y = 0 := by
    intro y
    have h1 : h.map (n - 1) (A := Subtype.val ⁻¹' (∅ : Set X)) (B := ∅) (incl univ)
        (fun _ hx => hx) (h.bd n univ ∅ y) = 0 := ((h.exact_right n hB) _).2 ⟨y, rfl⟩
    have h2 : h.bd n univ ∅ y = 0 :=
      (hbij (n - 1)).1 (by rw [h1, map_zero])
    obtain ⟨a, rfl⟩ := ((h.exact_mid n hB) y).1 h2
    exact hj0 a
  exact ⟨fun a b => by rw [hall a, hall b]⟩

/-- A space contractible to a point `t₀ ∈ S` by a homotopy keeping `S` inside `S` has
`H_n(T, S) = 0`. -/
theorem subsingleton_of_contraction (n : ℤ) {T : Type} [TopologicalSpace T] (S : Set T) (t₀ : T)
    (ht₀ : t₀ ∈ S) (E : (ContinuousMap.id T).Homotopy (ContinuousMap.const T t₀))
    (hE : ∀ t : I, MapsTo (fun x => E (t, x)) S S) : Subsingleton (h.H n T S) := by
  have := h.subsingleton_univ (X := Unit) n
  have hc1 : MapsTo (ContinuousMap.const T ()) S univ := fun _ _ => mem_univ _
  have hc2 : MapsTo (ContinuousMap.const Unit t₀) univ S := fun _ _ => ht₀
  have hall : ∀ a : h.H n T S, a = 0 := by
    intro a
    have e1 := DFunLike.congr_fun (h.homotopy n (ContinuousMap.id T) (ContinuousMap.const T t₀)
      (fun _ hx => hx) (fun _ _ => ht₀) E hE) a
    calc a = h.map n (ContinuousMap.id T) (fun _ hx => hx) a :=
          (h.map_id_apply n (ContinuousMap.id T) (fun _ hx => hx) rfl a).symm
      _ = h.map n (ContinuousMap.const T t₀) (fun _ _ => ht₀) a := e1
      _ = h.map n (ContinuousMap.const Unit t₀) hc2 (h.map n (ContinuousMap.const T ()) hc1 a) :=
          h.map_comp_apply n (ContinuousMap.const Unit t₀) (ContinuousMap.const T ())
            (ContinuousMap.const T t₀) hc2 hc1 (fun _ _ => ht₀) rfl a
      _ = 0 := by rw [Subsingleton.elim (h.map n (ContinuousMap.const T ()) hc1 a) 0, map_zero]
  exact ⟨fun a b => by rw [hall a, hall b]⟩

/-- A retract of a pair with vanishing `H_n` has vanishing `H_n`. -/
theorem subsingleton_of_retract (n : ℤ) {A : Set X} {B : Set Y} (φ : C(X, Y)) (χ : C(Y, X))
    (hφ : MapsTo φ A B) (hχ : MapsTo χ B A) (e : χ.comp φ = ContinuousMap.id X)
    (hY : Subsingleton (h.H n Y B)) : Subsingleton (h.H n X A) := by
  have hall : ∀ a : h.H n X A, a = 0 := by
    intro a
    rw [← h.map_map_eq_self n φ χ hφ hχ e a, Subsingleton.elim (h.map n φ hφ a) 0, map_zero]
  exact ⟨fun a b => by rw [hall a, hall b]⟩

/-- Exact sequence of a triple: if `H_n(A, B) = H_{n-1}(A, B) = 0`, then
`H_n(X, B) → H_n(X, A)` is bijective. -/
theorem bijective_of_triple (n : ℤ) {A B : Set X} (hBA : B ⊆ A)
    (h0 : Subsingleton (h.H n A (Subtype.val ⁻¹' B)))
    (h1 : Subsingleton (h.H (n - 1) A (Subtype.val ⁻¹' B))) :
    Function.Bijective (h.map n (A := B) (B := A) (ContinuousMap.id X) fun _ hx => hBA hx) := by
  refine ⟨(injective_iff_map_eq_zero _).2 fun a ha => ?_, fun y => ?_⟩
  · obtain ⟨b, rfl⟩ := ((h.exact_left n hBA) a).1 ha
    rw [Subsingleton.elim b 0, map_zero]
  · exact ((h.exact_mid n hBA) y).1 (Subsingleton.elim _ _)

/-- Excision, two-open-sets form: for open `A, U ⊆ X` with `A ∪ U = X`, the inclusion
`(U, U ∩ A) → (X, A)` induces isomorphisms. -/
theorem excision_open (n : ℤ) {A U : Set X} (hA : IsOpen A) (hU : IsOpen U)
    (hcov : A ∪ U = univ) :
    Function.Bijective (h.map n (A := Subtype.val ⁻¹' A) (B := A) (incl U) fun _ hx => hx) := by
  have key : ∀ Z : Set X, Zᶜ = U → Z ⊆ A → closure Z ⊆ interior A →
      Function.Bijective (h.map n (A := Subtype.val ⁻¹' A) (B := A) (incl U) fun _ hx => hx) := by
    rintro Z rfl hZA hcl
    exact h.excision n hZA hcl
  refine key Uᶜ (compl_compl U) ?_ ?_
  · intro x hx
    have : x ∈ A ∪ U := hcov ▸ mem_univ x
    exact this.resolve_right hx
  · rw [hU.isClosed_compl.closure_eq, hA.interior_eq]
    intro x hx
    have : x ∈ A ∪ U := hcov ▸ mem_univ x
    exact this.resolve_right hx

end General

end HomologyTheory

end LeanMisc.MATH518
