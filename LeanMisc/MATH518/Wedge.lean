import LeanMisc.MATH518.HomologyTheory

/-!
# MATH-518 (a): homology of a wedge

For good pairs `(X, x₀)`, `(Y, y₀)` (an open neighbourhood of the base point that deformation
retracts onto it, rel the base point), the map
`H̃_n(X) ⊕ H̃_n(Y) → H̃_n(X ∨ Y)`, `(a, b) ↦ (i_X)_* a + (i_Y)_* b`
is bijective for every `n`, where `H̃_n(X) = H_n(X, {x₀})` and `X ∨ Y = (X ⊔ Y)/(x₀ ∼ y₀)`.

Proof (wiki page 992, steps 2–5): `A = X ∨ V`, `B = U ∨ Y` are open (step 2), `X ↪ A`, `Y ↪ B`
are homotopy equivalences of pointed spaces and `A ∩ B = U ∨ V` is contractible (step 3);
step 4 (Mayer–Vietoris for an open cover with contractible intersection) is derived here from
the exact sequences of the triples `(X∨Y, A, *)`, `(A, A∩B, *)` and excision
(`HomologyTheory.bijective_sum_of_cover`).
-/

open Set Topology
open scoped unitInterval Classical

noncomputable section

namespace LeanMisc.MATH518

namespace HomologyTheory

variable (h : HomologyTheory)

/-- Mayer–Vietoris for an open cover `W = A ∪ B` with a base point `p ∈ A ∩ B`, in the case when
the maps `H_n(A, p) → H_n(A, A ∩ B)` and `H_n(B, p) → H_n(B, A ∩ B)` are bijective (e.g. when
`A ∩ B` is contractible): `H_n(A, p) ⊕ H_n(B, p) → H_n(W, p)` is bijective. -/
theorem bijective_sum_of_cover (n : ℤ) {W : Type} [TopologicalSpace W] {A B : Set W}
    (hA : IsOpen A) (hB : IsOpen B) (hcov : A ∪ B = univ) (p : W) (hpA : p ∈ A) (hpB : p ∈ B)
    (hkA : Function.Bijective (h.map n (A := Subtype.val ⁻¹' {p}) (B := Subtype.val ⁻¹' B)
      (ContinuousMap.id A) fun x (hx : x.1 = p) => show x.1 ∈ B from hx ▸ hpB))
    (hkB : Function.Bijective (h.map n (A := Subtype.val ⁻¹' {p}) (B := Subtype.val ⁻¹' A)
      (ContinuousMap.id B) fun x (hx : x.1 = p) => show x.1 ∈ A from hx ▸ hpA)) :
    Function.Bijective (fun q : h.H n A (Subtype.val ⁻¹' {p}) × h.H n B (Subtype.val ⁻¹' {p}) =>
      h.map n (B := {p}) (incl A) (fun _ hx => hx) q.1 +
        h.map n (B := {p}) (incl B) (fun _ hx => hx) q.2) := by
  have hpA' : ({p} : Set W) ⊆ A := singleton_subset_iff.2 hpA
  have hpB' : ({p} : Set W) ⊆ B := singleton_subset_iff.2 hpB
  set iA := h.map n (A := Subtype.val ⁻¹' {p}) (B := {p}) (incl A) (fun _ hx => hx) with hiA
  set iB := h.map n (A := Subtype.val ⁻¹' {p}) (B := {p}) (incl B) (fun _ hx => hx) with hiB
  set πA := h.map n (A := {p}) (B := A) (ContinuousMap.id W) (fun _ hx => hpA' hx) with hπA
  set πB := h.map n (A := {p}) (B := B) (ContinuousMap.id W) (fun _ hx => hpB' hx) with hπB
  -- excision
  have hexA := h.excision_open n hB hA (by rw [union_comm]; exact hcov)
  have hexB := h.excision_open n hA hB hcov
  -- `πB ∘ iA` and `πA ∘ iB` are bijective
  have hkA' : MapsTo (incl A) (Subtype.val ⁻¹' {p}) B :=
    fun x (hx : x.1 = p) => show x.1 ∈ B from hx ▸ hpB
  have hkB' : MapsTo (incl B) (Subtype.val ⁻¹' {p}) A :=
    fun x (hx : x.1 = p) => show x.1 ∈ A from hx ▸ hpA
  have hcA : Function.Bijective (fun a => πB (iA a)) := by
    have e : (fun a => πB (iA a)) =
        (h.map n (A := Subtype.val ⁻¹' B) (B := B) (incl A) fun _ hx => hx) ∘
          (h.map n (A := Subtype.val ⁻¹' {p}) (B := Subtype.val ⁻¹' B) (ContinuousMap.id A)
            fun x (hx : x.1 = p) => show x.1 ∈ B from hx ▸ hpB) := by
      funext a
      exact (h.map_comp_apply n (A := Subtype.val ⁻¹' {p}) (B := {p}) (C := B)
          (ContinuousMap.id W) (incl A) (incl A) (fun _ hx => hpB' hx) (fun _ hx => hx) hkA'
          rfl a).symm.trans
        (h.map_comp_apply n (A := Subtype.val ⁻¹' {p}) (B := Subtype.val ⁻¹' B) (C := B)
          (incl A) (ContinuousMap.id A) (incl A) (fun _ hx => hx)
          (fun x (hx : x.1 = p) => show x.1 ∈ B from hx ▸ hpB) hkA' rfl a)
    rw [e]
    exact hexA.comp hkA
  have hcB : Function.Bijective (fun b => πA (iB b)) := by
    have e : (fun b => πA (iB b)) =
        (h.map n (A := Subtype.val ⁻¹' A) (B := A) (incl B) fun _ hx => hx) ∘
          (h.map n (A := Subtype.val ⁻¹' {p}) (B := Subtype.val ⁻¹' A) (ContinuousMap.id B)
            fun x (hx : x.1 = p) => show x.1 ∈ A from hx ▸ hpA) := by
      funext b
      exact (h.map_comp_apply n (A := Subtype.val ⁻¹' {p}) (B := {p}) (C := A)
          (ContinuousMap.id W) (incl B) (incl B) (fun _ hx => hpA' hx) (fun _ hx => hx) hkB'
          rfl b).symm.trans
        (h.map_comp_apply n (A := Subtype.val ⁻¹' {p}) (B := Subtype.val ⁻¹' A) (C := A)
          (incl B) (ContinuousMap.id B) (incl B) (fun _ hx => hx)
          (fun x (hx : x.1 = p) => show x.1 ∈ A from hx ▸ hpA) hkB' rfl b)
    rw [e]
    exact hexB.comp hkB
  -- exactness of the triples `(W, A, p)` and `(W, B, p)` at `H_n(W, p)`
  have exA : ∀ w, πA w = 0 ↔ w ∈ range iA := fun w => (h.exact_left n hpA') w
  have exB : ∀ w, πB w = 0 ↔ w ∈ range iB := fun w => (h.exact_left n hpB') w
  have hAA : ∀ a, πA (iA a) = 0 := fun a => (exA _).2 ⟨a, rfl⟩
  have hBB : ∀ b, πB (iB b) = 0 := fun b => (exB _).2 ⟨b, rfl⟩
  let ψ := iA.coprod iB
  change Function.Bijective ψ
  refine ⟨(injective_iff_map_eq_zero ψ).2 ?_, fun w => ?_⟩
  · rintro ⟨a, b⟩ hab
    change iA a + iB b = 0 at hab
    have ha : πB (iA a) = 0 := by
      have := congrArg πB hab
      rwa [map_add, hBB, add_zero, map_zero] at this
    have hb : πA (iB b) = 0 := by
      have := congrArg πA hab
      rwa [map_add, hAA, zero_add, map_zero] at this
    have ha0 : a = 0 := hcA.1 (show πB (iA a) = πB (iA 0) by rw [ha, map_zero, map_zero])
    have hb0 : b = 0 := hcB.1 (show πA (iB b) = πA (iB 0) by rw [hb, map_zero, map_zero])
    rw [ha0, hb0, Prod.mk_zero_zero]
  · obtain ⟨b, hb⟩ := hcB.2 (πA w)
    have hb' : πA (iB b) = πA w := hb
    obtain ⟨a, ha⟩ := (exA (w - iB b)).1 (by rw [map_sub, hb', sub_self])
    exact ⟨(a, b), show iA a + iB b = w by rw [ha, sub_add_cancel]⟩

end HomologyTheory

variable {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]

/-- The relation gluing `x₀ ∈ X` to `y₀ ∈ Y`. -/
def WedgeRel (x₀ : X) (y₀ : Y) : X ⊕ Y → X ⊕ Y → Prop :=
  fun a b => a = Sum.inl x₀ ∧ b = Sum.inr y₀

/-- The wedge `X ∨ Y = (X ⊔ Y)/(x₀ ∼ y₀)`, with the quotient topology. -/
def Wedge (x₀ : X) (y₀ : Y) : Type := Quot (WedgeRel x₀ y₀)

instance (x₀ : X) (y₀ : Y) : TopologicalSpace (Wedge x₀ y₀) :=
  inferInstanceAs (TopologicalSpace (Quot (WedgeRel x₀ y₀)))

/-- A *good* base point: an open neighbourhood `U ∋ x₀` with a homotopy `F : I × U → U` from
the identity to the constant map at `x₀` that fixes `x₀` (a deformation retraction of `U` onto
`x₀`).  (Closedness of `{x₀}`, part of the usual definition, is not needed.) -/
structure GoodNbhd (x₀ : X) where
  U : Set X
  isOpen : IsOpen U
  mem : x₀ ∈ U
  F : C(I × U, U)
  F_zero : ∀ u, F (0, u) = u
  F_one : ∀ u, F (1, u) = ⟨x₀, mem⟩
  F_base : ∀ t, F (t, ⟨x₀, mem⟩) = ⟨x₀, mem⟩

namespace Wedge

variable (x₀ : X) (y₀ : Y)

/-- The quotient map `X ⊔ Y → X ∨ Y`. -/
def mk : X ⊕ Y → Wedge x₀ y₀ := Quot.mk _

theorem isQuotientMap_mk : IsQuotientMap (mk x₀ y₀) := isQuotientMap_quot_mk

theorem continuous_mk : Continuous (mk x₀ y₀) := continuous_quot_mk

theorem exists_rep (w : Wedge x₀ y₀) : ∃ s, mk x₀ y₀ s = w := Quot.exists_rep w

/-- The base point `* = [x₀] = [y₀]`. -/
def base : Wedge x₀ y₀ := mk x₀ y₀ (.inl x₀)

theorem mk_inr_y₀ : mk x₀ y₀ (.inr y₀) = base x₀ y₀ := (Quot.sound ⟨rfl, rfl⟩).symm

/-- `i_X : X → X ∨ Y`. -/
def inl : C(X, Wedge x₀ y₀) :=
  ⟨fun x => mk x₀ y₀ (.inl x), (continuous_mk x₀ y₀).comp continuous_inl⟩

/-- `i_Y : Y → X ∨ Y`. -/
def inr : C(Y, Wedge x₀ y₀) :=
  ⟨fun y => mk x₀ y₀ (.inr y), (continuous_mk x₀ y₀).comp continuous_inr⟩

theorem inl_mapsTo : MapsTo (inl x₀ y₀) {x₀} {base x₀ y₀} := by
  intro x hx
  rw [mem_singleton_iff] at hx
  subst hx
  exact mem_singleton _

theorem inr_mapsTo : MapsTo (inr x₀ y₀) {y₀} {base x₀ y₀} := by
  intro y hy
  rw [mem_singleton_iff] at hy
  rw [hy]
  exact mem_singleton_iff.2 (mk_inr_y₀ x₀ y₀)

/-- The subset `P ∨ Q ⊆ X ∨ Y` for `x₀ ∈ P`, `y₀ ∈ Q`. -/
def wset (P : Set X) (Q : Set Y) (hP : x₀ ∈ P) (hQ : y₀ ∈ Q) : Set (Wedge x₀ y₀) :=
  {w | Quot.lift (Sum.elim (· ∈ P) (· ∈ Q))
    (by rintro a b ⟨rfl, rfl⟩; exact propext (iff_of_true hP hQ)) w}

variable {x₀ y₀}

theorem isOpen_wset {P : Set X} {Q : Set Y} (hP : x₀ ∈ P) (hQ : y₀ ∈ Q) (hPo : IsOpen P)
    (hQo : IsOpen Q) : IsOpen (wset x₀ y₀ P Q hP hQ) :=
  (isQuotientMap_mk x₀ y₀).isOpen_preimage.1 (isOpen_sum_iff.2 ⟨hPo, hQo⟩)

/-- Continuity of a map out of `I × O`, `O ⊆ X ∨ Y` open, checked on the two pieces. -/
theorem continuous_of_pieces {Z : Type} [TopologicalSpace Z] (O : Set (Wedge x₀ y₀))
    (hO : IsOpen O) (g : I × O → Z)
    (hX : Continuous fun p : I × {x : X // mk x₀ y₀ (.inl x) ∈ O} =>
      g (p.1, ⟨mk x₀ y₀ (.inl p.2.1), p.2.2⟩))
    (hY : Continuous fun p : I × {y : Y // mk x₀ y₀ (.inr y) ∈ O} =>
      g (p.1, ⟨mk x₀ y₀ (.inr p.2.1), p.2.2⟩)) :
    Continuous g := by
  have hq : IsQuotientMap (O.restrictPreimage (mk x₀ y₀)) :=
    (isQuotientMap_mk x₀ y₀).restrictPreimage_isOpen hO
  refine hq.continuous_lift_prod_right ?_
  have hS : IsOpen (mk x₀ y₀ ⁻¹' O) := hO.preimage (continuous_mk x₀ y₀)
  rw [continuous_iff_continuousAt]
  rintro ⟨t, ⟨s | s, hs⟩⟩
  · let eX : {x : X // mk x₀ y₀ (.inl x) ∈ O} → (mk x₀ y₀ ⁻¹' O) := fun x => ⟨.inl x.1, x.2⟩
    have heX : IsOpenEmbedding eX := by
      rw [← IsOpenEmbedding.of_comp_iff eX hS.isOpenEmbedding_subtypeVal]
      exact IsOpenEmbedding.inl.comp
        (hS.preimage continuous_inl).isOpenEmbedding_subtypeVal
    have he : IsOpenEmbedding (Prod.map id eX : I × _ → I × _) :=
      IsOpenEmbedding.id.prodMap heX
    have key : ContinuousAt ((fun p : I × (mk x₀ y₀ ⁻¹' O) =>
        g (p.1, O.restrictPreimage (mk x₀ y₀) p.2)) ∘ Prod.map id eX) (t, ⟨s, hs⟩) :=
      hX.continuousAt
    exact he.continuousAt_iff.1 key
  · let eY : {y : Y // mk x₀ y₀ (.inr y) ∈ O} → (mk x₀ y₀ ⁻¹' O) := fun y => ⟨.inr y.1, y.2⟩
    have heY : IsOpenEmbedding eY := by
      rw [← IsOpenEmbedding.of_comp_iff eY hS.isOpenEmbedding_subtypeVal]
      exact IsOpenEmbedding.inr.comp
        (hS.preimage continuous_inr).isOpenEmbedding_subtypeVal
    have he : IsOpenEmbedding (Prod.map id eY : I × _ → I × _) :=
      IsOpenEmbedding.id.prodMap heY
    have key : ContinuousAt ((fun p : I × (mk x₀ y₀ ⁻¹' O) =>
        g (p.1, O.restrictPreimage (mk x₀ y₀) p.2)) ∘ Prod.map id eY) (t, ⟨s, hs⟩) :=
      hY.continuousAt
    exact he.continuousAt_iff.1 key

/-! ### The open cover `A = X ∨ V`, `B = U ∨ Y`, `A ∩ B = U ∨ V` -/

variable (gX : GoodNbhd x₀) (gY : GoodNbhd y₀)

/-- `A = X ∨ V`. -/
def setA : Set (Wedge x₀ y₀) := wset x₀ y₀ univ gY.U (mem_univ _) gY.mem
/-- `B = U ∨ Y`. -/
def setB : Set (Wedge x₀ y₀) := wset x₀ y₀ gX.U univ gX.mem (mem_univ _)
/-- `C = U ∨ V = A ∩ B`. -/
def setC : Set (Wedge x₀ y₀) := wset x₀ y₀ gX.U gY.U gX.mem gY.mem

theorem isOpen_setA : IsOpen (setA (x₀ := x₀) gY) := isOpen_wset _ _ isOpen_univ gY.isOpen
theorem isOpen_setB : IsOpen (setB (y₀ := y₀) gX) := isOpen_wset _ _ gX.isOpen isOpen_univ
theorem isOpen_setC : IsOpen (setC gX gY) := isOpen_wset _ _ gX.isOpen gY.isOpen

theorem cover : setA (x₀ := x₀) gY ∪ setB (y₀ := y₀) gX = univ := by
  refine eq_univ_of_forall fun w => ?_
  obtain ⟨s | s, rfl⟩ := exists_rep x₀ y₀ w
  · exact Or.inl (mem_univ s)
  · exact Or.inr (mem_univ s)

theorem base_mem_A : base x₀ y₀ ∈ setA (x₀ := x₀) gY := mem_univ x₀
theorem base_mem_B : base x₀ y₀ ∈ setB (y₀ := y₀) gX := gX.mem
theorem base_mem_C : base x₀ y₀ ∈ setC gX gY := gX.mem

theorem mem_C_of {w : Wedge x₀ y₀} (hA : w ∈ setA gY) (hB : w ∈ setB gX) : w ∈ setC gX gY := by
  obtain ⟨s | s, rfl⟩ := exists_rep x₀ y₀ w
  · exact hB
  · exact hA

theorem C_sub_A {w : Wedge x₀ y₀} (hC : w ∈ setC gX gY) : w ∈ setA gY := by
  obtain ⟨s | s, rfl⟩ := exists_rep x₀ y₀ w
  · exact mem_univ s
  · exact hC

theorem C_sub_B {w : Wedge x₀ y₀} (hC : w ∈ setC gX gY) : w ∈ setB gX := by
  obtain ⟨s | s, rfl⟩ := exists_rep x₀ y₀ w
  · exact hC
  · exact mem_univ s

/-! ### `X ↪ A` is a pointed homotopy equivalence -/

/-- The homotopy on `X ∨ Y` that contracts the `V`-part (meaningful on `A`). -/
def dA (t : I) : Wedge x₀ y₀ → Wedge x₀ y₀ :=
  Quot.lift (Sum.elim (fun x => mk x₀ y₀ (.inl x))
    (fun y => if hy : y ∈ gY.U then mk x₀ y₀ (.inr (gY.F (t, ⟨y, hy⟩)).1) else mk x₀ y₀ (.inr y)))
    (by
      rintro a b ⟨rfl, rfl⟩
      simp only [Sum.elim_inl, Sum.elim_inr]
      rw [dif_pos gY.mem, gY.F_base]
      exact (mk_inr_y₀ x₀ y₀).symm)

theorem dA_inl (t : I) (x : X) : dA gY t (mk x₀ y₀ (.inl x)) = mk x₀ y₀ (.inl x) := rfl

theorem dA_inr (t : I) {y : Y} (hy : y ∈ gY.U) :
    dA gY t (mk x₀ y₀ (.inr y)) = mk x₀ y₀ (.inr (gY.F (t, ⟨y, hy⟩)).1) := dif_pos hy

theorem dA_mem (t : I) {w : Wedge x₀ y₀} (hw : w ∈ setA gY) : dA gY t w ∈ setA gY := by
  obtain ⟨s | s, rfl⟩ := exists_rep x₀ y₀ w
  · exact mem_univ s
  · rw [dA_inr gY t hw]; exact (gY.F _).2

theorem continuous_dA : Continuous fun p : I × setA (x₀ := x₀) gY => dA gY p.1 p.2.1 := by
  refine continuous_of_pieces _ (isOpen_setA gY) _ ?_ ?_
  · exact (inl x₀ y₀).continuous.comp (continuous_subtype_val.comp continuous_snd)
  · have key : Continuous fun p : I × {y : Y // mk x₀ y₀ (.inr y) ∈ setA gY} =>
        mk x₀ y₀ (.inr (gY.F (p.1, ⟨p.2.1, p.2.2⟩)).1) :=
      (inr x₀ y₀).continuous.comp (continuous_subtype_val.comp (gY.F.continuous.comp
        (continuous_fst.prodMk ((continuous_subtype_val.comp continuous_snd).subtype_mk
          fun p => p.2.2))))
    exact key.congr fun p => (dA_inr gY p.1 p.2.2).symm

/-- `j_X : X → A`. -/
def jA : C(X, setA (x₀ := x₀) gY) :=
  ⟨fun x => ⟨mk x₀ y₀ (.inl x), mem_univ x⟩, (inl x₀ y₀).continuous.subtype_mk _⟩

/-- The retraction `A → X` (collapsing `V` to `x₀`). -/
def rAfun : Wedge x₀ y₀ → X :=
  Quot.lift (Sum.elim id fun _ => x₀) (by rintro a b ⟨rfl, rfl⟩; rfl)

def rA : C(setA (x₀ := x₀) gY, X) :=
  ⟨fun w => rAfun (x₀ := x₀) (y₀ := y₀) w.1, by
    have : Continuous fun p : I × setA (x₀ := x₀) gY => rAfun (x₀ := x₀) (y₀ := y₀) p.2.1 :=
      continuous_of_pieces _ (isOpen_setA gY) (fun p => rAfun (x₀ := x₀) (y₀ := y₀) p.2.1)
        (continuous_subtype_val.comp continuous_snd) continuous_const
    exact this.comp (Continuous.prodMk (f := fun _ => (0 : I)) continuous_const continuous_id)⟩

def DA : C(I × setA (x₀ := x₀) gY, setA (x₀ := x₀) gY) :=
  ⟨fun p => ⟨dA gY p.1 p.2.1, dA_mem gY p.1 p.2.2⟩, (continuous_dA gY).subtype_mk _⟩

def homA : (ContinuousMap.id (setA (x₀ := x₀) gY)).Homotopy ((jA gY).comp (rA gY)) where
  toContinuousMap := DA gY
  map_zero_left w := by
    rcases w with ⟨w, hw⟩
    obtain ⟨s | s, rfl⟩ := exists_rep x₀ y₀ w
    · rfl
    · apply Subtype.ext
      change dA gY 0 (mk x₀ y₀ (.inr s)) = mk x₀ y₀ (.inr s)
      rw [dA_inr gY 0 hw, gY.F_zero]
  map_one_left w := by
    rcases w with ⟨w, hw⟩
    obtain ⟨s | s, rfl⟩ := exists_rep x₀ y₀ w
    · rfl
    · apply Subtype.ext
      change dA gY 1 (mk x₀ y₀ (.inr s)) = mk x₀ y₀ (.inl x₀)
      rw [dA_inr gY 1 hw, gY.F_one]
      exact mk_inr_y₀ x₀ y₀

theorem jA_mapsTo : MapsTo (jA (x₀ := x₀) gY) {x₀} (Subtype.val ⁻¹' {base x₀ y₀}) :=
  fun x hx => inl_mapsTo x₀ y₀ hx

theorem rA_mapsTo : MapsTo (rA (x₀ := x₀) gY) (Subtype.val ⁻¹' {base x₀ y₀}) {x₀} := by
  intro w (hw : w.1 = base x₀ y₀)
  change rAfun (x₀ := x₀) (y₀ := y₀) w.1 ∈ ({x₀} : Set X)
  rw [hw]
  exact mem_singleton _

theorem homA_rel (t : I) : MapsTo (fun w => homA gY (t, w)) (Subtype.val ⁻¹' {base x₀ y₀})
    (Subtype.val ⁻¹' {base x₀ y₀}) := by
  intro w (hw : w.1 = base x₀ y₀)
  change dA gY t w.1 ∈ ({base x₀ y₀} : Set (Wedge x₀ y₀))
  rw [hw]
  exact mem_singleton _

/-! ### `Y ↪ B` is a pointed homotopy equivalence -/

def dB (t : I) : Wedge x₀ y₀ → Wedge x₀ y₀ :=
  Quot.lift (Sum.elim
    (fun x => if hx : x ∈ gX.U then mk x₀ y₀ (.inl (gX.F (t, ⟨x, hx⟩)).1) else mk x₀ y₀ (.inl x))
    (fun y => mk x₀ y₀ (.inr y)))
    (by
      rintro a b ⟨rfl, rfl⟩
      simp only [Sum.elim_inl, Sum.elim_inr]
      rw [dif_pos gX.mem, gX.F_base]
      exact Quot.sound ⟨rfl, rfl⟩)

theorem dB_inr (t : I) (y : Y) : dB gX t (mk x₀ y₀ (.inr y)) = mk x₀ y₀ (.inr y) := rfl

theorem dB_inl (t : I) {x : X} (hx : x ∈ gX.U) :
    dB gX t (mk x₀ y₀ (.inl x)) = mk x₀ y₀ (.inl (gX.F (t, ⟨x, hx⟩)).1) := dif_pos hx

theorem dB_mem (t : I) {w : Wedge x₀ y₀} (hw : w ∈ setB gX) : dB gX t w ∈ setB gX := by
  obtain ⟨s | s, rfl⟩ := exists_rep x₀ y₀ w
  · rw [dB_inl gX t hw]; exact (gX.F _).2
  · exact mem_univ s

theorem continuous_dB : Continuous fun p : I × setB (y₀ := y₀) gX => dB gX p.1 p.2.1 := by
  refine continuous_of_pieces _ (isOpen_setB gX) _ ?_ ?_
  · have key : Continuous fun p : I × {x : X // mk x₀ y₀ (.inl x) ∈ setB gX} =>
        mk x₀ y₀ (.inl (gX.F (p.1, ⟨p.2.1, p.2.2⟩)).1) :=
      (inl x₀ y₀).continuous.comp (continuous_subtype_val.comp (gX.F.continuous.comp
        (continuous_fst.prodMk ((continuous_subtype_val.comp continuous_snd).subtype_mk
          fun p => p.2.2))))
    exact key.congr fun p => (dB_inl gX p.1 p.2.2).symm
  · exact (inr x₀ y₀).continuous.comp (continuous_subtype_val.comp continuous_snd)

def jB : C(Y, setB (y₀ := y₀) gX) :=
  ⟨fun y => ⟨mk x₀ y₀ (.inr y), mem_univ y⟩, (inr x₀ y₀).continuous.subtype_mk _⟩

def rBfun : Wedge x₀ y₀ → Y :=
  Quot.lift (Sum.elim (fun _ => y₀) id) (by rintro a b ⟨rfl, rfl⟩; rfl)

def rB : C(setB (y₀ := y₀) gX, Y) :=
  ⟨fun w => rBfun (x₀ := x₀) (y₀ := y₀) w.1, by
    have : Continuous fun p : I × setB (y₀ := y₀) gX => rBfun (x₀ := x₀) (y₀ := y₀) p.2.1 :=
      continuous_of_pieces _ (isOpen_setB gX) (fun p => rBfun (x₀ := x₀) (y₀ := y₀) p.2.1)
        continuous_const (continuous_subtype_val.comp continuous_snd)
    exact this.comp (Continuous.prodMk (f := fun _ => (0 : I)) continuous_const continuous_id)⟩

def DB : C(I × setB (y₀ := y₀) gX, setB (y₀ := y₀) gX) :=
  ⟨fun p => ⟨dB gX p.1 p.2.1, dB_mem gX p.1 p.2.2⟩, (continuous_dB gX).subtype_mk _⟩

def homB : (ContinuousMap.id (setB (y₀ := y₀) gX)).Homotopy ((jB gX).comp (rB gX)) where
  toContinuousMap := DB gX
  map_zero_left w := by
    rcases w with ⟨w, hw⟩
    obtain ⟨s | s, rfl⟩ := exists_rep x₀ y₀ w
    · apply Subtype.ext
      change dB gX 0 (mk x₀ y₀ (.inl s)) = mk x₀ y₀ (.inl s)
      rw [dB_inl gX 0 hw, gX.F_zero]
    · rfl
  map_one_left w := by
    rcases w with ⟨w, hw⟩
    obtain ⟨s | s, rfl⟩ := exists_rep x₀ y₀ w
    · apply Subtype.ext
      change dB gX 1 (mk x₀ y₀ (.inl s)) = mk x₀ y₀ (.inr y₀)
      rw [dB_inl gX 1 hw, gX.F_one]
      exact (mk_inr_y₀ x₀ y₀).symm
    · rfl

theorem jB_mapsTo : MapsTo (jB (y₀ := y₀) gX) {y₀} (Subtype.val ⁻¹' {base x₀ y₀}) :=
  fun y hy => inr_mapsTo x₀ y₀ hy

theorem rB_mapsTo : MapsTo (rB (y₀ := y₀) gX) (Subtype.val ⁻¹' {base x₀ y₀}) {y₀} := by
  intro w (hw : w.1 = base x₀ y₀)
  change rBfun (x₀ := x₀) (y₀ := y₀) w.1 ∈ ({y₀} : Set Y)
  rw [hw]
  exact mem_singleton _

theorem homB_rel (t : I) : MapsTo (fun w => homB gX (t, w)) (Subtype.val ⁻¹' {base x₀ y₀})
    (Subtype.val ⁻¹' {base x₀ y₀}) := by
  intro w (hw : w.1 = base x₀ y₀)
  change dB gX t w.1 ∈ ({base x₀ y₀} : Set (Wedge x₀ y₀))
  rw [hw]
  change dB gX t (mk x₀ y₀ (.inl x₀)) ∈ _
  rw [dB_inl gX t gX.mem, gX.F_base]
  exact mem_singleton _

/-! ### `C = U ∨ V` is contractible rel `*` -/

def dC (t : I) : Wedge x₀ y₀ → Wedge x₀ y₀ :=
  Quot.lift (Sum.elim
    (fun x => if hx : x ∈ gX.U then mk x₀ y₀ (.inl (gX.F (t, ⟨x, hx⟩)).1) else mk x₀ y₀ (.inl x))
    (fun y => if hy : y ∈ gY.U then mk x₀ y₀ (.inr (gY.F (t, ⟨y, hy⟩)).1) else mk x₀ y₀ (.inr y)))
    (by
      rintro a b ⟨rfl, rfl⟩
      simp only [Sum.elim_inl, Sum.elim_inr]
      rw [dif_pos gX.mem, gX.F_base, dif_pos gY.mem, gY.F_base]
      exact Quot.sound ⟨rfl, rfl⟩)

theorem dC_inl (t : I) {x : X} (hx : x ∈ gX.U) :
    dC gX gY t (mk x₀ y₀ (.inl x)) = mk x₀ y₀ (.inl (gX.F (t, ⟨x, hx⟩)).1) := dif_pos hx

theorem dC_inr (t : I) {y : Y} (hy : y ∈ gY.U) :
    dC gX gY t (mk x₀ y₀ (.inr y)) = mk x₀ y₀ (.inr (gY.F (t, ⟨y, hy⟩)).1) := dif_pos hy

theorem dC_mem (t : I) {w : Wedge x₀ y₀} (hw : w ∈ setC gX gY) : dC gX gY t w ∈ setC gX gY := by
  obtain ⟨s | s, rfl⟩ := exists_rep x₀ y₀ w
  · rw [dC_inl gX gY t hw]; exact (gX.F _).2
  · rw [dC_inr gX gY t hw]; exact (gY.F _).2

theorem continuous_dC : Continuous fun p : I × setC gX gY => dC gX gY p.1 p.2.1 := by
  refine continuous_of_pieces _ (isOpen_setC gX gY) _ ?_ ?_
  · have key : Continuous fun p : I × {x : X // mk x₀ y₀ (.inl x) ∈ setC gX gY} =>
        mk x₀ y₀ (.inl (gX.F (p.1, ⟨p.2.1, p.2.2⟩)).1) :=
      (inl x₀ y₀).continuous.comp (continuous_subtype_val.comp (gX.F.continuous.comp
        (continuous_fst.prodMk ((continuous_subtype_val.comp continuous_snd).subtype_mk
          fun p => p.2.2))))
    exact key.congr fun p => (dC_inl gX gY p.1 p.2.2).symm
  · have key : Continuous fun p : I × {y : Y // mk x₀ y₀ (.inr y) ∈ setC gX gY} =>
        mk x₀ y₀ (.inr (gY.F (p.1, ⟨p.2.1, p.2.2⟩)).1) :=
      (inr x₀ y₀).continuous.comp (continuous_subtype_val.comp (gY.F.continuous.comp
        (continuous_fst.prodMk ((continuous_subtype_val.comp continuous_snd).subtype_mk
          fun p => p.2.2))))
    exact key.congr fun p => (dC_inr gX gY p.1 p.2.2).symm

def baseC : setC gX gY := ⟨base x₀ y₀, base_mem_C gX gY⟩

def homC : (ContinuousMap.id (setC gX gY)).Homotopy (ContinuousMap.const _ (baseC gX gY)) where
  toFun p := ⟨dC gX gY p.1 p.2.1, dC_mem gX gY p.1 p.2.2⟩
  continuous_toFun := (continuous_dC gX gY).subtype_mk _
  map_zero_left w := by
    rcases w with ⟨w, hw⟩
    obtain ⟨s | s, rfl⟩ := exists_rep x₀ y₀ w
    · apply Subtype.ext
      change dC gX gY 0 (mk x₀ y₀ (.inl s)) = mk x₀ y₀ (.inl s)
      rw [dC_inl gX gY 0 hw, gX.F_zero]
    · apply Subtype.ext
      change dC gX gY 0 (mk x₀ y₀ (.inr s)) = mk x₀ y₀ (.inr s)
      rw [dC_inr gX gY 0 hw, gY.F_zero]
  map_one_left w := by
    rcases w with ⟨w, hw⟩
    obtain ⟨s | s, rfl⟩ := exists_rep x₀ y₀ w
    · apply Subtype.ext
      change dC gX gY 1 (mk x₀ y₀ (.inl s)) = mk x₀ y₀ (.inl x₀)
      rw [dC_inl gX gY 1 hw, gX.F_one]
    · apply Subtype.ext
      change dC gX gY 1 (mk x₀ y₀ (.inr s)) = mk x₀ y₀ (.inl x₀)
      rw [dC_inr gX gY 1 hw, gY.F_one]
      exact mk_inr_y₀ x₀ y₀

theorem homC_rel (t : I) : MapsTo (fun w => homC gX gY (t, w)) (Subtype.val ⁻¹' {base x₀ y₀})
    (Subtype.val ⁻¹' {base x₀ y₀}) := by
  intro w (hw : w.1 = base x₀ y₀)
  change dC gX gY t w.1 ∈ ({base x₀ y₀} : Set (Wedge x₀ y₀))
  rw [hw]
  change dC gX gY t (mk x₀ y₀ (.inl x₀)) ∈ _
  rw [dC_inl gX gY t gX.mem, gX.F_base]
  exact mem_singleton _

end Wedge

open Wedge

namespace HomologyTheory

variable (h : HomologyTheory) {x₀ : X} {y₀ : Y}

theorem subsingleton_C (gX : GoodNbhd x₀) (gY : GoodNbhd y₀) (k : ℤ) :
    Subsingleton (h.H k (setC gX gY) (Subtype.val ⁻¹' {base x₀ y₀})) :=
  h.subsingleton_of_contraction k _ (baseC gX gY) rfl (homC gX gY) (homC_rel gX gY)

/-- `H_k(A ∩ B, *) = 0`, with `A ∩ B` seen as a subspace of `A`. -/
theorem subsingleton_BinA (gX : GoodNbhd x₀) (gY : GoodNbhd y₀) (k : ℤ) :
    Subsingleton (h.H k (Subtype.val ⁻¹' setB (y₀ := y₀) gX : Set (setA (x₀ := x₀) gY))
      (Subtype.val ⁻¹' (Subtype.val ⁻¹' {base x₀ y₀}))) :=
  h.subsingleton_of_retract k
    (⟨fun z => ⟨z.1.1, mem_C_of gX gY z.1.2 z.2⟩,
      (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _⟩ :
      C(_, setC gX gY))
    ⟨fun c => ⟨⟨c.1, C_sub_A gX gY c.2⟩, C_sub_B gX gY c.2⟩,
      (continuous_subtype_val.subtype_mk _).subtype_mk _⟩
    (fun _ hz => hz) (fun _ hc => hc) (ContinuousMap.ext fun _ => rfl) (h.subsingleton_C gX gY k)

/-- `H_k(A ∩ B, *) = 0`, with `A ∩ B` seen as a subspace of `B`. -/
theorem subsingleton_AinB (gX : GoodNbhd x₀) (gY : GoodNbhd y₀) (k : ℤ) :
    Subsingleton (h.H k (Subtype.val ⁻¹' setA (x₀ := x₀) gY : Set (setB (y₀ := y₀) gX))
      (Subtype.val ⁻¹' (Subtype.val ⁻¹' {base x₀ y₀}))) :=
  h.subsingleton_of_retract k
    (⟨fun z => ⟨z.1.1, mem_C_of gX gY z.2 z.1.2⟩,
      (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _⟩ :
      C(_, setC gX gY))
    ⟨fun c => ⟨⟨c.1, C_sub_B gX gY c.2⟩, C_sub_A gX gY c.2⟩,
      (continuous_subtype_val.subtype_mk _).subtype_mk _⟩
    (fun _ hz => hz) (fun _ hc => hc) (ContinuousMap.ext fun _ => rfl) (h.subsingleton_C gX gY k)

/-- **MATH-518 (a)** (claim `thm:wedge`, wiki page 992).  For good pairs `(X, x₀)`, `(Y, y₀)`
and every `n`, the map `H̃_n(X) ⊕ H̃_n(Y) → H̃_n(X ∨ Y)`, `(a, b) ↦ (i_X)_* a + (i_Y)_* b`,
is bijective; here `H̃_n(X) = H_n(X, {x₀})`. -/
theorem wedge_bijective (gX : GoodNbhd x₀) (gY : GoodNbhd y₀) (n : ℤ) :
    Function.Bijective (fun q : h.H n X {x₀} × h.H n Y {y₀} =>
      h.map n (inl x₀ y₀) (inl_mapsTo x₀ y₀) q.1 + h.map n (inr x₀ y₀) (inr_mapsTo x₀ y₀) q.2) := by
  -- step 3: `X → A` and `Y → B` induce isomorphisms
  have hjA : Function.Bijective (h.map n (jA (x₀ := x₀) gY) (jA_mapsTo (x₀ := x₀) gY)) :=
    h.bijective_of_retract n (jA (x₀ := x₀) gY) (rA (x₀ := x₀) gY) (jA_mapsTo (x₀ := x₀) gY) (rA_mapsTo (x₀ := x₀) gY)
      (ContinuousMap.ext fun _ => rfl) (homA (x₀ := x₀) gY) (homA_rel (x₀ := x₀) gY)
  have hjB : Function.Bijective (h.map n (jB (y₀ := y₀) gX) (jB_mapsTo (y₀ := y₀) gX)) :=
    h.bijective_of_retract n (jB (y₀ := y₀) gX) (rB (y₀ := y₀) gX) (jB_mapsTo (y₀ := y₀) gX) (rB_mapsTo (y₀ := y₀) gX)
      (ContinuousMap.ext fun _ => rfl) (homB (y₀ := y₀) gX) (homB_rel (y₀ := y₀) gX)
  -- step 4: Mayer–Vietoris for the cover `A ∪ B`
  have hkA := h.bijective_of_triple n
    (X := setA (x₀ := x₀) gY) (A := Subtype.val ⁻¹' setB (y₀ := y₀) gX)
    (B := Subtype.val ⁻¹' {base x₀ y₀})
    (fun x (hx : x.1 = base x₀ y₀) => show x.1 ∈ setB gX from hx ▸ base_mem_B gX)
    (h.subsingleton_BinA gX gY n) (h.subsingleton_BinA gX gY (n - 1))
  have hkB := h.bijective_of_triple n
    (X := setB (y₀ := y₀) gX) (A := Subtype.val ⁻¹' setA (x₀ := x₀) gY)
    (B := Subtype.val ⁻¹' {base x₀ y₀})
    (fun x (hx : x.1 = base x₀ y₀) => show x.1 ∈ setA gY from hx ▸ base_mem_A gY)
    (h.subsingleton_AinB gX gY n) (h.subsingleton_AinB gX gY (n - 1))
  have hψ := h.bijective_sum_of_cover n (isOpen_setA gY) (isOpen_setB gX) (cover gX gY)
    (base x₀ y₀) (base_mem_A gY) (base_mem_B gX) hkA hkB
  -- step 5: `Φ = ψ ∘ (j_X × j_Y)`
  have e : (fun q : h.H n X {x₀} × h.H n Y {y₀} =>
      h.map n (inl x₀ y₀) (inl_mapsTo x₀ y₀) q.1 + h.map n (inr x₀ y₀) (inr_mapsTo x₀ y₀) q.2) =
      (fun q : h.H n (setA (x₀ := x₀) gY) (Subtype.val ⁻¹' {base x₀ y₀}) ×
          h.H n (setB (y₀ := y₀) gX) (Subtype.val ⁻¹' {base x₀ y₀}) =>
        h.map n (B := {base x₀ y₀}) (incl (setA (x₀ := x₀) gY)) (fun _ hx => hx) q.1 +
          h.map n (B := {base x₀ y₀}) (incl (setB (y₀ := y₀) gX)) (fun _ hx => hx) q.2) ∘
        Prod.map (h.map n (jA (x₀ := x₀) gY) (jA_mapsTo (x₀ := x₀) gY)) (h.map n (jB (y₀ := y₀) gX) (jB_mapsTo (y₀ := y₀) gX)) := by
    funext q
    simp only [Function.comp_apply, Prod.map_fst, Prod.map_snd]
    rw [h.map_comp_apply n (incl _) (jA (x₀ := x₀) gY) (inl x₀ y₀) (fun _ hx => hx) (jA_mapsTo (x₀ := x₀) gY)
        (inl_mapsTo x₀ y₀) rfl,
      h.map_comp_apply n (incl _) (jB (y₀ := y₀) gX) (inr x₀ y₀) (fun _ hx => hx) (jB_mapsTo (y₀ := y₀) gX)
        (inr_mapsTo x₀ y₀) rfl]
  rw [e]
  exact hψ.comp ⟨hjA.1.prodMap hjB.1, hjA.2.prodMap hjB.2⟩

/-- The isomorphism `H̃_n(X) ⊕ H̃_n(Y) ≃+ H̃_n(X ∨ Y)` of `wedge_bijective`. -/
def wedgeEquiv (gX : GoodNbhd x₀) (gY : GoodNbhd y₀) (n : ℤ) : h.H n X {x₀} × h.H n Y {y₀} ≃+ h.H n (Wedge x₀ y₀) {base x₀ y₀} :=
  AddEquiv.ofBijective ((h.map n (inl x₀ y₀) (inl_mapsTo x₀ y₀)).coprod
    (h.map n (inr x₀ y₀) (inr_mapsTo x₀ y₀))) (h.wedge_bijective gX gY n)

end HomologyTheory

end LeanMisc.MATH518
