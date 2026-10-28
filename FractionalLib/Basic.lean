/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Mathlib
public import FractionalLib.FiniteLPDuality

/-!
# Fractional colourings and fractional cliques

A fractional colouring of a finite graph `G` puts a nonnegative weight on every vertex set,
zero on non-independent sets, so that every vertex is covered with total weight at least `1`.
The fractional chromatic number `χ_f(G)` is the infimum of the total weights. A fractional
clique is a nonnegative vertex weighting giving every independent set total weight at most `1`.

* `IsFracClique.sum_le` — weak duality: a fractional clique weighs at most any fractional
  colouring;
* `one_le_fracChromaticNumber` — `1 ≤ χ_f(G)` on a nonempty vertex type;
* `exists_fracClique_eq` — strong duality: some fractional clique weighs exactly `χ_f(G)`
  (from `FiniteLP.covering_packing_duality`).
-/

@[expose] public section

open Finset

namespace FractionalColouring

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)

/-- A fractional colouring: nonnegative weights on vertex sets, vanishing off independent
sets, covering every vertex with total weight at least `1`. -/
def IsFracColouring (x : Finset V → ℝ) : Prop :=
  (∀ s, 0 ≤ x s) ∧ (∀ s : Finset V, ¬ G.IsIndepSet (s : Set V) → x s = 0) ∧
    ∀ v, 1 ≤ ∑ s ∈ univ.filter (fun s => v ∈ s), x s

/-- The fractional chromatic number `χ_f(G)`. -/
noncomputable def fracChromaticNumber : ℝ :=
  sInf {t | ∃ x, IsFracColouring G x ∧ t = ∑ s, x s}

/-- A fractional clique: nonnegative vertex weights with total at most `1` on every
independent set. -/
def IsFracClique (g : V → ℝ) : Prop :=
  (∀ v, 0 ≤ g v) ∧ ∀ s : Finset V, G.IsIndepSet (s : Set V) → ∑ v ∈ s, g v ≤ 1

variable {G}

/-- The set of fractional-colouring weights is bounded below by `0`. -/
theorem bddBelow_weights : BddBelow {t | ∃ x, IsFracColouring G x ∧ t = ∑ s, x s} :=
  ⟨0, by
    rintro _ ⟨x, hx, rfl⟩
    exact Finset.sum_nonneg fun s _ => hx.1 s⟩

/-- The colouring by singletons. -/
noncomputable def singletonColouring : Finset V → ℝ := fun s => if s.card = 1 then 1 else 0

theorem isFracColouring_singletons : IsFracColouring G singletonColouring := by
  refine ⟨fun s => by unfold singletonColouring; split_ifs <;> norm_num, fun s hs => ?_,
    fun v => ?_⟩
  · unfold singletonColouring
    rw [if_neg]
    intro h
    obtain ⟨a, rfl⟩ := Finset.card_eq_one.mp h
    exact hs (by simp)
  · refine le_trans ?_ (Finset.single_le_sum (f := singletonColouring)
      (fun s _ => by unfold singletonColouring; split_ifs <;> norm_num)
      (Finset.mem_filter.mpr ⟨Finset.mem_univ {v}, Finset.mem_singleton_self v⟩))
    simp [singletonColouring]

/-- The set of fractional-colouring weights is nonempty. -/
theorem weights_nonempty : {t | ∃ x, IsFracColouring G x ∧ t = ∑ s, x s}.Nonempty :=
  ⟨_, _, isFracColouring_singletons, rfl⟩

/-- Any fractional colouring weighs at least `χ_f(G)`. -/
theorem fracChromaticNumber_le {x : Finset V → ℝ} (hx : IsFracColouring G x) :
    fracChromaticNumber G ≤ ∑ s, x s :=
  csInf_le bddBelow_weights ⟨x, hx, rfl⟩

/-- Exchange of summation for a vertex weighting against a fractional colouring. -/
theorem sum_mul_cover (g : V → ℝ) (x : Finset V → ℝ) (T : Finset V) :
    ∑ v ∈ T, g v * ∑ s ∈ univ.filter (fun s => v ∈ s), x s =
      ∑ s, x s * ∑ v ∈ T ∩ s, g v := by
  calc ∑ v ∈ T, g v * ∑ s ∈ univ.filter (fun s => v ∈ s), x s
        = ∑ v ∈ T, ∑ s, if v ∈ s then g v * x s else 0 := by
          refine Finset.sum_congr rfl fun v _ => ?_
          rw [Finset.sum_filter, Finset.mul_sum]
          exact Finset.sum_congr rfl fun s _ => by split_ifs <;> simp
    _ = ∑ s, ∑ v ∈ T, if v ∈ s then g v * x s else 0 := Finset.sum_comm
    _ = ∑ s, x s * ∑ v ∈ T ∩ s, g v := by
          refine Finset.sum_congr rfl fun s _ => ?_
          rw [← Finset.sum_filter, Finset.filter_mem_eq_inter, Finset.mul_sum]
          exact Finset.sum_congr rfl fun v _ => by ring

/-- **Local weak duality.** If every independent set meets `T` in `g`-weight at most `c`, then
`g(T) ≤ c · w(x)` for every fractional colouring `x`. -/
theorem sum_le_mul_of_indep {g : V → ℝ} (hg : ∀ v, 0 ≤ g v) {T : Finset V} {c : ℝ}
    (hc : ∀ s : Finset V, G.IsIndepSet (s : Set V) → ∑ v ∈ T ∩ s, g v ≤ c)
    {x : Finset V → ℝ} (hx : IsFracColouring G x) :
    ∑ v ∈ T, g v ≤ c * ∑ s, x s := by
  calc ∑ v ∈ T, g v ≤ ∑ v ∈ T, g v * ∑ s ∈ univ.filter (fun s => v ∈ s), x s :=
        Finset.sum_le_sum fun v _ => le_mul_of_one_le_right (hg v) (hx.2.2 v)
    _ = ∑ s, x s * ∑ v ∈ T ∩ s, g v := sum_mul_cover g x T
    _ ≤ ∑ s, x s * c := by
        refine Finset.sum_le_sum fun s _ => ?_
        by_cases hs : G.IsIndepSet (s : Set V)
        · exact mul_le_mul_of_nonneg_left (hc s hs) (hx.1 s)
        · rw [hx.2.1 s hs]; simp
    _ = c * ∑ s, x s := by rw [← Finset.sum_mul, mul_comm]

/-- **Weak duality.** A fractional clique weighs at most any fractional colouring. -/
theorem IsFracClique.sum_le {g : V → ℝ} (hg : IsFracClique G g) {x : Finset V → ℝ}
    (hx : IsFracColouring G x) : ∑ v, g v ≤ ∑ s, x s := by
  have := sum_le_mul_of_indep (T := univ) hg.1 (c := 1)
    (fun s hs => by rw [Finset.univ_inter]; exact hg.2 s hs) hx
  simpa using this

/-- A fractional clique weighs at most `χ_f(G)`. -/
theorem IsFracClique.sum_le_fracChromaticNumber {g : V → ℝ} (hg : IsFracClique G g) :
    ∑ v, g v ≤ fracChromaticNumber G :=
  le_csInf weights_nonempty (by rintro _ ⟨x, hx, rfl⟩; exact hg.sum_le hx)

/-- If `g(T) ≤ c · w(x)` for every fractional colouring `x` and `c ≥ 0`, then
`g(T) ≤ c · χ_f(G)`. -/
theorem le_mul_fracChromaticNumber {a c : ℝ} (hc : 0 ≤ c)
    (h : ∀ x, IsFracColouring G x → a ≤ c * ∑ s, x s) : a ≤ c * fracChromaticNumber G := by
  rcases hc.eq_or_lt with rfl | hc
  · simpa using h _ isFracColouring_singletons
  · rw [← div_le_iff₀' hc]
    exact le_csInf weights_nonempty (by
      rintro _ ⟨x, hx, rfl⟩
      rw [div_le_iff₀' hc]
      exact h x hx)

/-- `1 ≤ χ_f(G)` on a nonempty vertex type. -/
theorem one_le_fracChromaticNumber [Nonempty V] : 1 ≤ fracChromaticNumber G := by
  obtain ⟨v⟩ := ‹Nonempty V›
  have hg : IsFracClique G (fun u => if u = v then 1 else 0) := by
    refine ⟨fun u => by dsimp only; split_ifs <;> norm_num, fun s _ => ?_⟩
    rw [Finset.sum_ite_eq']
    split_ifs <;> norm_num
  simpa using hg.sum_le_fracChromaticNumber

open Classical in
/-- **Strong duality.** Some fractional clique weighs exactly `χ_f(G)`. -/
theorem exists_fracClique_eq : ∃ g, IsFracClique G g ∧ ∑ v, g v = fracChromaticNumber G := by
  let A : Finset V → V → ℝ := fun s v => if v ∈ s ∧ G.IsIndepSet (s : Set V) then 1 else 0
  obtain ⟨w, hw0, hwle, hweq⟩ := FiniteLP.covering_packing_duality A (fun _ => 1)
    (fun s v => by dsimp only [A]; split_ifs <;> norm_num) (fun _ => zero_le_one)
    (fun v => ⟨{v}, by simp [A]⟩)
  refine ⟨w, ⟨hw0, fun s hs => ?_⟩, ?_⟩
  · have := hwle s
    simp only [A, hs, and_true, ite_mul, one_mul, zero_mul] at this
    rwa [← Finset.sum_filter, Finset.filter_mem_eq_inter, Finset.univ_inter] at this
  · rw [hweq]
    -- the covering LP of `A` has the same infimum as `χ_f(G)`
    apply le_antisymm
    · refine le_csInf weights_nonempty ?_
      rintro _ ⟨x, hx, rfl⟩
      refine csInf_le ⟨0, ?_⟩ ⟨x, hx.1, fun v => ?_, by simp⟩
      · rintro _ ⟨y, hy, -, rfl⟩
        exact Finset.sum_nonneg fun s _ => by simpa using hy s
      · refine le_trans (hx.2.2 v) (le_of_eq ?_)
        rw [Finset.sum_filter]
        refine Finset.sum_congr rfl fun s _ => ?_
        by_cases hvs : v ∈ s
        · by_cases hs : G.IsIndepSet (s : Set V)
          · simp [A, hvs, hs]
          · simp [A, hvs, hs, hx.2.1 s hs]
        · simp [A, hvs]
    · refine le_csInf ⟨_, fun _ => 1, fun _ => zero_le_one, fun v => ?_, rfl⟩ ?_
      · exact le_trans (by simp [A]) (Finset.single_le_sum (f := fun s => A s v * 1)
          (fun s _ => by dsimp only [A]; split_ifs <;> norm_num) (Finset.mem_univ {v}))
      · rintro _ ⟨y, hy0, hycov, rfl⟩
        let x : Finset V → ℝ := fun s => if G.IsIndepSet (s : Set V) then y s else 0
        have hx : IsFracColouring G x := by
          refine ⟨fun s => by dsimp only [x]; split_ifs <;> simp [hy0 s], fun s hs => by
            simp [x, hs], fun v => ?_⟩
          refine le_trans (hycov v) (le_of_eq ?_)
          rw [Finset.sum_filter]
          refine Finset.sum_congr rfl fun s _ => ?_
          by_cases hvs : v ∈ s <;> by_cases hs : G.IsIndepSet (s : Set V) <;> simp [A, x, hvs, hs]
        refine le_trans (fracChromaticNumber_le hx) (Finset.sum_le_sum fun s _ => ?_)
        dsimp only [x]
        split_ifs <;> simp [hy0 s]

end FractionalColouring
