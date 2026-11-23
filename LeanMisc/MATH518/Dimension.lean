import LeanMisc.MATH518.HomologyTheory

/-!
# MATH-518 (b): topological invariance of dimension

A topological `m`-manifold here is a space in which every point has a neighbourhood (in the
sense of `𝓝 x`, not necessarily open) homeomorphic to `ℝ^m`; no Hausdorff or countability
assumption.  From the axioms of `HomologyTheory` together with `PointAxiom` and `SphereAxiom`:

* `t1Space_of_isTopManifold` — such a space is `T₁` (Lemma 2 of wiki page 992);
* `nontrivial_euclid_iff` — `H_k(ℝ^m, ℝ^m ∖ 0) ≠ 0 ↔ k = m` (Lemma 3);
* `nontrivial_local_iff` — `H_k(M, M ∖ x) ≠ 0 ↔ k = m` (Lemma 4, via excision);
* `dim_eq_of_homeomorph` — homeomorphic nonempty manifolds have equal dimension (claim `thm:dim`).
-/

open Set Topology Metric
open scoped unitInterval

noncomputable section

namespace LeanMisc.MATH518

/-- `M` is a topological manifold of dimension `m`: every point has a neighbourhood
homeomorphic to `ℝ^m`.  No Hausdorff or second-countability assumption. -/
def IsTopManifold (M : Type) [TopologicalSpace M] (m : ℕ) : Prop :=
  ∀ x : M, ∃ N ∈ 𝓝 x, Nonempty (N ≃ₜ EuclideanSpace ℝ (Fin m))

/-- Lemma 2: a manifold (in the above sense) is a `T₁` space. -/
theorem t1Space_of_isTopManifold {M : Type} [TopologicalSpace M] {m : ℕ}
    (hM : IsTopManifold M m) : T1Space M := by
  rw [t1Space_iff_exists_open]
  intro x y hxy
  obtain ⟨N, hN, ⟨χ⟩⟩ := hM x
  obtain ⟨W, hWN, hWo, hxW⟩ := mem_nhds_iff.1 hN
  haveI : T1Space N := χ.isEmbedding.t1Space
  by_cases hy : y ∈ N
  · have hS : IsOpen (Subtype.val ⁻¹' W ∩ {(⟨y, hy⟩ : N)}ᶜ) :=
      (hWo.preimage continuous_subtype_val).inter isOpen_compl_singleton
    obtain ⟨O, hO, hOS⟩ := isOpen_induced_iff.1 hS
    refine ⟨O ∩ W, hO.inter hWo, ⟨?_, hxW⟩, fun hyU => ?_⟩
    · have : (⟨x, hWN hxW⟩ : N) ∈ Subtype.val ⁻¹' W ∩ {(⟨y, hy⟩ : N)}ᶜ :=
        ⟨hxW, fun h => hxy (congrArg Subtype.val h)⟩
      rw [← hOS] at this
      exact this
    · have : (⟨y, hy⟩ : N) ∈ Subtype.val ⁻¹' O := hyU.1
      rw [hOS] at this
      exact this.2 rfl
  · exact ⟨W, hWo, hxW, fun hyW => hy (hWN hyW)⟩

namespace HomologyTheory

variable (h : HomologyTheory)

/-- Local homology is invariant under open embeddings: for an open embedding `e : P → M` into a
`T₁` space, `e_* : H_n(P, P ∖ p) → H_n(M, M ∖ e p)` is bijective (excision). -/
theorem bijective_local_of_isOpenEmbedding (n : ℤ) {P M : Type} [TopologicalSpace P]
    [TopologicalSpace M] [T1Space M] (e : C(P, M)) (he : IsOpenEmbedding e) (p : P) :
    Function.Bijective (h.map n (A := {p}ᶜ) (B := {e p}ᶜ) e
      fun _ hq hq' => hq (he.injective hq')) := by
  set U := range e with hU
  have hUo : IsOpen U := he.isOpen_range
  have hAo : IsOpen ({e p}ᶜ : Set M) := isOpen_compl_singleton
  have hcov : ({e p}ᶜ : Set M) ∪ U = univ := by
    refine eq_univ_of_forall fun z => ?_
    by_cases hz : z = e p
    · exact Or.inr ⟨p, hz.symm⟩
    · exact Or.inl hz
  have hexc := h.excision_open n hAo hUo hcov
  let φ : P ≃ₜ U := he.toIsEmbedding.toHomeomorph
  have hφ : ∀ q, (φ q : M) = e q := fun q => rfl
  have hφA : MapsTo φ ({p}ᶜ : Set P) (Subtype.val ⁻¹' ({e p}ᶜ : Set M)) := by
    intro q hq hq'
    exact hq (he.injective (by rw [← hφ q]; exact hq'))
  have hφB : MapsTo φ.symm (Subtype.val ⁻¹' ({e p}ᶜ : Set M)) ({p}ᶜ : Set P) := by
    intro u hu hu'
    apply hu
    change (u : M) = e p
    rw [← φ.apply_symm_apply u, hφ, show φ.symm u = p from hu']
  have hbφ := h.bijective_of_homeomorph n φ hφA hφB
  have e' : (h.map n (A := {p}ᶜ) (B := {e p}ᶜ) e fun _ hq hq' => hq (he.injective hq')) =
      (h.map n (A := Subtype.val ⁻¹' {e p}ᶜ) (B := {e p}ᶜ) (incl U) fun _ hx => hx) ∘
        (h.map n (φ : C(P, U)) hφA) := by
    funext a
    exact h.map_comp_apply n (A := {p}ᶜ) (B := Subtype.val ⁻¹' {e p}ᶜ) (C := {e p}ᶜ)
      (incl U) (φ : C(P, U)) e (fun _ hx => hx) hφA _
      (ContinuousMap.ext fun q => hφ q) a
  rw [e']
  exact hexc.comp hbφ

/-- Lemma 3: `H_k(ℝ^m, ℝ^m ∖ 0)` is nontrivial iff `k = m`. -/
theorem nontrivial_euclid_iff (hpt : h.PointAxiom) (hS : h.SphereAxiom) (m : ℕ) (k : ℤ) :
    Nontrivial (h.H k (EuclideanSpace ℝ (Fin m)) {0}ᶜ) ↔ k = m := by
  cases m with
  | zero =>
    -- `ℝ^0` is a point and `ℝ^0 ∖ 0 = ∅`
    have h0 : ∀ v : EuclideanSpace ℝ (Fin 0), v = 0 := fun v => PiLp.ext fun i => i.elim0
    let f : C(EuclideanSpace ℝ (Fin 0), Unit) := ContinuousMap.const _ ()
    let g : C(Unit, EuclideanSpace ℝ (Fin 0)) := ContinuousMap.const _ 0
    have hf : MapsTo f ({0}ᶜ : Set (EuclideanSpace ℝ (Fin 0))) ∅ := fun v hv => hv (h0 v)
    have hg : MapsTo g (∅ : Set Unit) {0}ᶜ := fun _ hx => (hx : False).elim
    have hb : Function.Bijective (h.map k f hf) :=
      h.bijective_of_inverse k f g hf hg
        (h.map_map_eq_self k f g hf hg (ContinuousMap.ext fun v => (h0 v).symm))
        (h.map_map_eq_self k g f hg hf (ContinuousMap.ext fun _ => rfl))
    exact (h.nontrivial_congr hb).trans ((h.nontrivial_iff_of (hpt k).1 (hpt k).2).trans
      (by omega))
  | succ m =>
    let R := EuclideanSpace ℝ (Fin (m + 1))
    let O : Set R := {0}ᶜ
    let p : R := (spherePt m).1
    have hp1 : ‖p‖ = 1 := mem_sphere_zero_iff_norm.1 (spherePt m).2
    have hpO : p ∈ O := fun hp0 => by
      have : ‖p‖ = 0 := by rw [show p = 0 from hp0, norm_zero]
      rw [hp1] at this
      exact one_ne_zero this
    have hpO' : ({p} : Set R) ⊆ O := singleton_subset_iff.2 hpO
    -- `ℝ^{m+1}` contracts to `p` (straight-line homotopy), so `H_*(ℝ^{m+1}, p) = 0`
    let L : (ContinuousMap.id R).Homotopy (ContinuousMap.const R p) :=
      { toFun := fun q => (1 - (q.1 : ℝ)) • q.2 + (q.1 : ℝ) • p
        continuous_toFun := by fun_prop
        map_zero_left := fun v => by simp
        map_one_left := fun v => by simp }
    have hL : ∀ t : I, MapsTo (fun v => L (t, v)) {p} {p} := by
      intro t v hv
      rw [mem_singleton_iff] at hv ⊢
      change (1 - (t : ℝ)) • v + (t : ℝ) • p = p
      rw [hv, ← add_smul, sub_add_cancel, one_smul]
    have hRp : ∀ j : ℤ, Subsingleton (h.H j R {p}) := fun j =>
      h.subsingleton_of_contraction j {p} p rfl L hL
    -- the boundary `H_k(ℝ^{m+1}, O) → H_{k-1}(O, p)` is bijective
    have hbd : Function.Bijective (h.bd k O {p}) := by
      haveI := hRp k
      haveI := hRp (k - 1)
      refine ⟨(injective_iff_map_eq_zero _).2 fun y hy => ?_, fun z => ?_⟩
      · obtain ⟨a, rfl⟩ := ((h.exact_mid k hpO') y).1 hy
        rw [Subsingleton.elim a 0, map_zero]
      · exact ((h.exact_right k hpO') z).1 (Subsingleton.elim _ _)
    -- `S^m ↪ ℝ^{m+1} ∖ 0` is a homotopy equivalence of pairs (radial retraction)
    let S := sphere (0 : R) 1
    have hS0 : ∀ s : S, (s : R) ≠ 0 := fun s hs0 => by
      have : ‖(s : R)‖ = 1 := mem_sphere_zero_iff_norm.1 s.2
      rw [hs0, norm_zero] at this
      exact zero_ne_one this
    let ι : C(S, O) := ⟨fun s => ⟨s.1, hS0 s⟩, continuous_subtype_val.subtype_mk _⟩
    have hnorm : ∀ v : O, ‖(v : R)‖ ≠ 0 := fun v => norm_ne_zero_iff.2 v.2
    let ρ : C(O, S) := ⟨fun v => ⟨‖(v : R)‖⁻¹ • (v : R), mem_sphere_zero_iff_norm.2 (by
        rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ (hnorm v)])⟩,
      (((continuous_norm.comp continuous_subtype_val).inv₀ hnorm).smul
        continuous_subtype_val).subtype_mk _⟩
    have hcoef : ∀ (t : I) (v : O), 0 < (1 - (t : ℝ)) + (t : ℝ) * ‖(v : R)‖⁻¹ := by
      intro t v
      have ht0 : 0 ≤ (t : ℝ) := unitInterval.nonneg t
      have ht1 : (t : ℝ) ≤ 1 := unitInterval.le_one t
      have hc : 0 < ‖(v : R)‖⁻¹ := inv_pos.2 (norm_pos_iff.2 v.2)
      rcases eq_or_lt_of_le ht0 with h0 | h0
      · rw [← h0]; norm_num
      · have := mul_pos h0 hc
        linarith
    let G : (ContinuousMap.id O).Homotopy (ι.comp ρ) :=
      { toFun := fun q => ⟨((1 - (q.1 : ℝ)) + (q.1 : ℝ) * ‖(q.2 : R)‖⁻¹) • (q.2 : R),
          smul_ne_zero (hcoef q.1 q.2).ne' q.2.2⟩
        continuous_toFun := by
          refine Continuous.subtype_mk ?_ _
          refine Continuous.smul ?_ (continuous_subtype_val.comp continuous_snd)
          refine (continuous_const.sub (continuous_subtype_val.comp continuous_fst)).add
            ((continuous_subtype_val.comp continuous_fst).mul ?_)
          exact (continuous_norm.comp (continuous_subtype_val.comp continuous_snd)).inv₀
            fun q => hnorm q.2
        map_zero_left := fun v => by
          apply Subtype.ext
          change ((1 - ((0 : I) : ℝ)) + ((0 : I) : ℝ) * ‖(v : R)‖⁻¹) • (v : R) = (v : R)
          simp
        map_one_left := fun v => by
          apply Subtype.ext
          change ((1 - ((1 : I) : ℝ)) + ((1 : I) : ℝ) * ‖(v : R)‖⁻¹) • (v : R) =
            ‖(v : R)‖⁻¹ • (v : R)
          simp }
    have hιA : MapsTo ι {spherePt m} (Subtype.val ⁻¹' {p}) := by
      intro s hs
      rw [mem_singleton_iff] at hs
      subst hs
      exact rfl
    have hρA : MapsTo ρ (Subtype.val ⁻¹' {p}) {spherePt m} := by
      intro v (hv : (v : R) = p)
      refine mem_singleton_iff.2 (Subtype.ext ?_)
      change ‖(v : R)‖⁻¹ • (v : R) = p
      rw [hv, hp1, inv_one, one_smul]
    have hG : ∀ t : I, MapsTo (fun v => G (t, v)) (Subtype.val ⁻¹' {p}) (Subtype.val ⁻¹' {p}) := by
      intro t v (hv : (v : R) = p)
      change ((1 - (t : ℝ)) + (t : ℝ) * ‖(v : R)‖⁻¹) • (v : R) = p
      rw [hv, hp1, inv_one, mul_one, sub_add_cancel, one_smul]
    have hιρ : ρ.comp ι = ContinuousMap.id S := by
      refine ContinuousMap.ext fun s => Subtype.ext ?_
      change ‖(s : R)‖⁻¹ • (s : R) = s
      rw [mem_sphere_zero_iff_norm.1 s.2, inv_one, one_smul]
    have hbι : Function.Bijective (h.map (k - 1) ι hιA) :=
      h.bijective_of_retract (k - 1) ι ρ hιA hρA hιρ G hG
    exact (h.nontrivial_congr hbd).trans ((h.nontrivial_congr hbι).symm.trans
      ((h.nontrivial_iff_of (hS m (k - 1)).1 (hS m (k - 1)).2).trans (by omega)))

/-- Lemma 4: for an `m`-manifold `M` and `x ∈ M`, `H_k(M, M ∖ x)` is nontrivial iff `k = m`. -/
theorem nontrivial_local_iff (hpt : h.PointAxiom) (hS : h.SphereAxiom) {M : Type}
    [TopologicalSpace M] {m : ℕ} (hM : IsTopManifold M m) (x : M) (k : ℤ) :
    Nontrivial (h.H k M {x}ᶜ) ↔ k = m := by
  haveI := t1Space_of_isTopManifold hM
  obtain ⟨N, hN, ⟨χ⟩⟩ := hM x
  obtain ⟨W, hWN, hWo, hxW⟩ := mem_nhds_iff.1 hN
  let P := (Subtype.val ⁻¹' W : Set N)
  have hPo : IsOpen P := hWo.preimage continuous_subtype_val
  let p : P := ⟨⟨x, hWN hxW⟩, hxW⟩
  -- `e₁ : P → M` and `e₂ : P → ℝ^m` are open embeddings
  let e₁ : C(P, M) := ⟨fun q => q.1.1, continuous_subtype_val.comp continuous_subtype_val⟩
  have he₁ : IsOpenEmbedding e₁ := by
    refine ⟨IsEmbedding.subtypeVal.comp IsEmbedding.subtypeVal, ?_⟩
    have : range e₁ = W := by
      ext z
      constructor
      · rintro ⟨q, rfl⟩
        exact q.2
      · intro hz
        exact ⟨⟨⟨z, hWN hz⟩, hz⟩, rfl⟩
    rw [this]
    exact hWo
  let c : EuclideanSpace ℝ (Fin m) := χ ⟨x, hWN hxW⟩
  let e₂ : C(P, EuclideanSpace ℝ (Fin m)) :=
    ⟨fun q => χ q.1 - c, (χ.continuous.comp continuous_subtype_val).sub continuous_const⟩
  have he₂ : IsOpenEmbedding e₂ :=
    ((Homeomorph.subRight c).isOpenEmbedding.comp χ.isOpenEmbedding).comp
      hPo.isOpenEmbedding_subtypeVal
  have h₁ := h.nontrivial_congr (h.bijective_local_of_isOpenEmbedding k e₁ he₁ p)
  have h₂ := h.nontrivial_congr (h.bijective_local_of_isOpenEmbedding k e₂ he₂ p)
  have hc : e₂ p = 0 := sub_self c
  rw [hc] at h₂
  change Nontrivial (h.H k P {p}ᶜ) ↔ Nontrivial (h.H k M {x}ᶜ) at h₁
  rw [← h₁, h₂]
  exact h.nontrivial_euclid_iff hpt hS m k

/-- **MATH-518 (b)** (claim `thm:dim`, wiki page 992): if nonempty topological manifolds `M`
(of dimension `m`) and `N` (of dimension `n`) are homeomorphic, then `m = n`.  Proved for any
homology theory satisfying the axioms of `HomologyTheory`, `PointAxiom` and `SphereAxiom`. -/
theorem dim_eq_of_homeomorph (hpt : h.PointAxiom) (hS : h.SphereAxiom) {M N : Type}
    [TopologicalSpace M] [TopologicalSpace N] {m n : ℕ} (hM : IsTopManifold M m)
    (hN : IsTopManifold N n) [Nonempty M] (f : M ≃ₜ N) : m = n := by
  let x : M := Classical.arbitrary M
  have hA : MapsTo f ({x}ᶜ : Set M) {f x}ᶜ := fun _ hy hy' => hy (f.injective hy')
  have hB : MapsTo f.symm ({f x}ᶜ : Set N) {x}ᶜ := fun y hy hy' => hy (show y = f x by
    rw [← f.apply_symm_apply y, show f.symm y = x from hy'])
  have hb := h.bijective_of_homeomorph (m : ℤ) f hA hB
  have hm : Nontrivial (h.H m M {x}ᶜ) := (h.nontrivial_local_iff hpt hS hM x m).2 rfl
  have hn : Nontrivial (h.H m N {f x}ᶜ) := (h.nontrivial_congr hb).1 hm
  exact_mod_cast (h.nontrivial_local_iff hpt hS hN (f x) m).1 hn

end HomologyTheory

end LeanMisc.MATH518
