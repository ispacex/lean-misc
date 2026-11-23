# lean-misc

Lean 4 / Mathlib formalizations of miscellaneous problems (MATH tracker, wiki «Разные задачи»).

Toolchain `leanprover/lean4:v4.35.0`, Mathlib `v4.35.0` (rev `56a005855ea17e0b0958f73ec801ae140b0a1679`),
pinned in `lean-toolchain` and `lake-manifest.json`.

```sh
lake exe cache get
lake build
lake env lean LeanMisc/MATH518/Audit.lean   # #print axioms of the main theorems
```

## Problems

| Issue | Wiki | Lean | What |
|---|---|---|---|
| MATH-518 | [page 992](https://default.kaiku.tech/wiki/MATH?page=992) | `LeanMisc/MATH518/` | homology of a wedge; topological invariance of dimension |

## MATH-518

Problem 6 (AT): (a) for good pairs, `H̃_n(X ∨ Y) ≅ H̃_n(X) ⊕ H̃_n(Y)`; (b) homeomorphic nonempty
topological manifolds (no Hausdorff assumption) have the same dimension.

**What is verified.** The *logic* of the solution on wiki page 992, from explicit axioms of a homology
theory. Mathlib at this revision defines singular homology but does not prove exactness or excision
for it (it has `TopPair.HomologyPretheory` with homotopy invariance only), so singular homology itself
is **not** shown to satisfy the axioms. All point-set topology is proved in Lean; nothing is `sorry`,
and no `axiom` is declared.

### Assumptions (everything a reader has to trust)

`LeanMisc/MATH518/HomologyTheory.lean`, structure `HomologyTheory` — groups `H n X A = H_n(X, A)`
(`n : ℤ`, `X : Type` a topological space, `A : Set X`) with

| field | axiom |
|---|---|
| `map`, `map_id`, `map_comp` | functoriality on maps of pairs |
| `homotopy` | maps of pairs homotopic through maps of pairs induce the same map |
| `bd`, `exact_left`, `exact_mid`, `exact_right` | long exact sequence of a triple `B ⊆ A ⊆ X`: `H_n(A,B) → H_n(X,B) → H_n(X,A) → H_{n-1}(A,B) → H_{n-1}(X,B)` |
| `excision` | `Z ⊆ A ⊆ X`, `closure Z ⊆ interior A` ⇒ `(X∖Z, A∖Z) ↪ (X, A)` induces isomorphisms |

and, for part (b) only, two hypotheses on the theory:

| hypothesis | statement |
|---|---|
| `PointAxiom` | `H_k(pt) ≅ ℤ` for `k = 0`, `H_k(pt) = 0` for `k ≠ 0` |
| `SphereAxiom` | for all `m ≥ 0`: `H_k(S^m, e₀) ≅ ℤ` for `k = m`, `= 0` for `k ≠ m` (`S^m` the unit sphere of `ℝ^{m+1}`) |

Naturality of `∂`, additivity and Mayer–Vietoris are **not** assumed; the needed case of
Mayer–Vietoris is derived (`HomologyTheory.bijective_sum_of_cover`). `HomologyTheory.trivial`
(the zero theory) shows that the fields are consistent (it fails `PointAxiom`, as it must).

Modelling choices: reduced homology of a pointed space is `H̃_n(X) := H_n(X, {x₀})`; a *good* base
point (`GoodNbhd x₀`) is an open `U ∋ x₀` with a deformation retraction of `U` onto `x₀` rel `x₀`
(closedness of `{x₀}` is not needed); an `m`-manifold (`IsTopManifold M m`) is a space in which
every point has a neighbourhood (`N ∈ 𝓝 x`, not necessarily open) homeomorphic to `ℝ^m`.

### Main statements

* `HomologyTheory.wedge_bijective h gX gY n` — `(a, b) ↦ (i_X)_* a + (i_Y)_* b`,
  `H_n(X, x₀) × H_n(Y, y₀) → H_n(X ∨ Y, *)`, is bijective (claim `thm:wedge`);
  `HomologyTheory.wedgeEquiv` is the resulting `≃+`.
* `HomologyTheory.dim_eq_of_homeomorph h hpt hS hM hN f : m = n` (claim `thm:dim`).
* Lemmas of page 992: `t1Space_of_isTopManifold` (Lemma 2), `nontrivial_euclid_iff` (Lemma 3),
  `nontrivial_local_iff` (Lemma 4), `bijective_local_of_isOpenEmbedding` (excision step).

`#print axioms` of the main theorems: `[propext, Classical.choice, Quot.sound]`.
