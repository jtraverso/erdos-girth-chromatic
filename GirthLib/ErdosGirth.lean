/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Mathlib
public import GirthLib.ErdosGirthAux

/-!
# Erdős' theorem: graphs of large girth and large chromatic number

**Erdős (1959).** For every `g` and every `k` there is a finite graph with girth greater than `g`
and chromatic number greater than `k`. Erdős proved this with the probabilistic method, and the
proof gives more: for every `ε > 0` and all large `n` there is a graph on `n` vertices with girth
greater than `g` whose independent sets all have fewer than `ε n` vertices.

* `ErdosGirth.exists_girth_indep`: for every `g` and `ε > 0`, for all sufficiently large `n` there
  is a graph on `Fin n` with extended girth (Mathlib's `SimpleGraph.egirth`) greater than `g` in
  which every independent set has fewer than `ε n` vertices.
* `ErdosGirth.exists_girth_not_colorable`: for every `g` and `k`, for all sufficiently large `n`
  there is a graph on `Fin n` with girth greater than `g` that is not `k`-colourable.
* `ErdosGirth.exists_girth_chromaticNumber`: **Erdős' theorem.** For every `g` and `k` there is a
  finite graph with girth greater than `g` and chromatic number greater than `k`.
-/

@[expose] public section

open Finset SimpleGraph

namespace ErdosGirth

/-- **Erdős (1959), structural form.** For every `g` and every `ε > 0`, for all sufficiently large
`n` there is a graph on `n` vertices with no cycle of length at most `g` in which every independent
set has fewer than `ε n` vertices. -/
theorem exists_girth_indep (g : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n ≥ N, ∃ G : SimpleGraph (Fin n), (g : ℕ∞) < G.egirth ∧
      ∀ s : Finset (Fin n), G.IsIndepSet (s : Set (Fin n)) → (s.card : ℝ) < ε * n := by
  obtain ⟨N, hN0, hN⟩ := exists_params g hε
  refine ⟨N, fun n hn => ?_⟩
  obtain ⟨p, t, hp0, hp1, ht, hineq⟩ := hN n hn
  obtain ⟨G, D, hD, hcyc, hind⟩ := exists_good_graph (2 * n) g t hp0 hp1 (by omega) hineq
  obtain ⟨H, hH, hHind⟩ := exists_of_deletion n g t G D hD hcyc hind
  refine ⟨H, hH, fun s hs => ?_⟩
  calc (s.card : ℝ) < t := by exact_mod_cast hHind s hs
    _ ≤ ε * n := ht

/-- For every `g` and `k`, for all sufficiently large `n` there is a graph on `n` vertices with
no cycle of length at most `g` that is not `k`-colourable. -/
theorem exists_girth_not_colorable (g k : ℕ) :
    ∃ N : ℕ, ∀ n ≥ N, ∃ G : SimpleGraph (Fin n), (g : ℕ∞) < G.egirth ∧ ¬ G.Colorable k := by
  obtain ⟨N, hN⟩ := exists_girth_indep g (ε := 1 / (k + 1)) (by positivity)
  refine ⟨max N 1, fun n hn => ?_⟩
  obtain ⟨G, hG, hind⟩ := hN n (le_of_max_le_left hn)
  refine ⟨G, hG, fun ⟨C⟩ => ?_⟩
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast le_of_max_le_right hn
  have hcls : ∀ c : Fin k,
      ((univ.filter (fun v => C v = c)).card : ℝ) < 1 / (k + 1) * n := by
    intro c
    refine hind _ ?_
    intro x hx y hy _ hadj
    simp only [coe_filter, mem_univ, true_and] at hx hy
    exact C.valid hadj (hx.trans hy.symm)
  have hsum : (n : ℝ) = ∑ c : Fin k, ((univ.filter (fun v => C v = c)).card : ℝ) := by
    have := card_eq_sum_card_fiberwise (f := C) (s := univ) (t := univ) (fun _ _ => mem_univ _)
    rw [card_univ, Fintype.card_fin] at this
    exact_mod_cast this
  have hle : (n : ℝ) ≤ k * (1 / (k + 1) * n) := by
    calc (n : ℝ) = _ := hsum
      _ ≤ ∑ _c : Fin k, 1 / ((k : ℝ) + 1) * n := sum_le_sum fun c _ => (hcls c).le
      _ = _ := by rw [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hk : (k : ℝ) * (1 / (k + 1) * n) < n := by
    rw [← mul_assoc, mul_one_div]
    have hk0 : (0 : ℝ) < k + 1 := by positivity
    have : (k : ℝ) / (k + 1) < 1 := by rw [div_lt_one hk0]; linarith
    nlinarith
  linarith

/-- **Erdős' theorem (1959).** For every `g` and `k` there is a finite graph with girth greater
than `g` and chromatic number greater than `k`. -/
theorem exists_girth_chromaticNumber (g k : ℕ) :
    ∃ (n : ℕ) (G : SimpleGraph (Fin n)), (g : ℕ∞) < G.egirth ∧ (k : ℕ∞) < G.chromaticNumber := by
  obtain ⟨N, hN⟩ := exists_girth_not_colorable g k
  obtain ⟨G, hG, hc⟩ := hN N le_rfl
  exact ⟨N, G, hG, lt_of_not_ge fun h => hc (chromaticNumber_le_iff_colorable.mp h)⟩

end ErdosGirth
