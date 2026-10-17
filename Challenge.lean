/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Mathlib

/-!
# Erdős' theorem: graphs of large girth and large chromatic number

**Erdős (1959).** For every `g` and every `k` there is a finite graph with girth greater than `g`
and chromatic number greater than `k`. Erdős proved this with the probabilistic method, and the
proof gives more: for every `ε > 0` and all large `n` there is a graph on `n` vertices with girth
greater than `g` whose independent sets all have fewer than `ε n` vertices.

* `ErdosGirthChromatic.exists_girth_indep`: for every `g` and `ε > 0`, for all sufficiently large `n` there
  is a graph on `Fin n` with extended girth (Mathlib's `SimpleGraph.egirth`) greater than `g` in
  which every independent set has fewer than `ε n` vertices.
* `ErdosGirthChromatic.exists_girth_not_colorable`: for every `g` and `k`, for all sufficiently large `n`
  there is a graph on `Fin n` with girth greater than `g` that is not `k`-colourable.
* `ErdosGirthChromatic.exists_girth_chromaticNumber`: **Erdős' theorem.** For every `g` and `k` there is a
  finite graph with girth greater than `g` and chromatic number greater than `k`.

The Mathlib definitions used in these statements are reproduced verbatim, with file and line at the
pinned Mathlib revision, in `MATHLIB_DEFINITIONS.md` at the root of this repository.
-/

@[expose] public section

open Finset SimpleGraph

namespace ErdosGirthChromatic

/-- **Erdős (1959), structural form.** For every `g` and every `ε > 0`, for all sufficiently large
`n` there is a graph on `n` vertices with no cycle of length at most `g` in which every independent
set has fewer than `ε n` vertices. -/
theorem exists_girth_indep (g : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n ≥ N, ∃ G : SimpleGraph (Fin n), (g : ℕ∞) < G.egirth ∧
      ∀ s : Finset (Fin n), G.IsIndepSet (s : Set (Fin n)) → (s.card : ℝ) < ε * n := by
  sorry

/-- For every `g` and `k`, for all sufficiently large `n` there is a graph on `n` vertices with
no cycle of length at most `g` that is not `k`-colourable. -/
theorem exists_girth_not_colorable (g k : ℕ) :
    ∃ N : ℕ, ∀ n ≥ N, ∃ G : SimpleGraph (Fin n), (g : ℕ∞) < G.egirth ∧ ¬ G.Colorable k := by
  sorry

/-- **Erdős' theorem (1959).** For every `g` and `k` there is a finite graph with girth greater
than `g` and chromatic number greater than `k`. -/
theorem exists_girth_chromaticNumber (g k : ℕ) :
    ∃ (n : ℕ) (G : SimpleGraph (Fin n)), (g : ℕ∞) < G.egirth ∧ (k : ℕ∞) < G.chromaticNumber := by
  sorry

end ErdosGirthChromatic
