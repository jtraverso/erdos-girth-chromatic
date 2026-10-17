/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Mathlib
public import GirthLib.ErdosGirth

/-!
# Proofs of the statements in `Challenge.lean`

The theorems are proved in `GirthLib/ErdosGirth.lean` and `GirthLib/ErdosGirthAux.lean`
(namespace `ErdosGirth`) by Erdős's probabilistic method, written with explicit finite weighted
sums: graphs on `2n` vertices are weighted by `p^{|E|}(1 − p)^{(2n choose 2) − |E|}`, the expected
number of short cycles and of independent `t`-sets is bounded, a good graph is chosen, one vertex is
deleted from each short cycle, and the graph induced on `n` of the remaining vertices is taken.
-/

@[expose] public section

open Finset SimpleGraph

namespace ErdosGirthChromatic

/-- **Erdős (1959), structural form.** For every `g` and every `ε > 0`, for all sufficiently large
`n` there is a graph on `n` vertices with no cycle of length at most `g` in which every independent
set has fewer than `ε n` vertices. -/
theorem exists_girth_indep (g : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n ≥ N, ∃ G : SimpleGraph (Fin n), (g : ℕ∞) < G.egirth ∧
      ∀ s : Finset (Fin n), G.IsIndepSet (s : Set (Fin n)) → (s.card : ℝ) < ε * n :=
  ErdosGirth.exists_girth_indep g hε

/-- For every `g` and `k`, for all sufficiently large `n` there is a graph on `n` vertices with
no cycle of length at most `g` that is not `k`-colourable. -/
theorem exists_girth_not_colorable (g k : ℕ) :
    ∃ N : ℕ, ∀ n ≥ N, ∃ G : SimpleGraph (Fin n), (g : ℕ∞) < G.egirth ∧ ¬ G.Colorable k :=
  ErdosGirth.exists_girth_not_colorable g k

/-- **Erdős' theorem (1959).** For every `g` and `k` there is a finite graph with girth greater
than `g` and chromatic number greater than `k`. -/
theorem exists_girth_chromaticNumber (g k : ℕ) :
    ∃ (n : ℕ) (G : SimpleGraph (Fin n)), (g : ℕ∞) < G.egirth ∧ (k : ℕ∞) < G.chromaticNumber :=
  ErdosGirth.exists_girth_chromaticNumber g k

end ErdosGirthChromatic
