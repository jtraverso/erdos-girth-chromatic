/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Mathlib

/-!
# Auxiliary lemmas for Erdős' girth/chromatic number theorem

The random graph `G(m, p)` is modelled by explicit weights on the finsets of off-diagonal
pairs of `Fin m`; first-moment estimates are explicit weighted sums.
-/

@[expose] public section

open Finset SimpleGraph

namespace ErdosGirth

/-- The off-diagonal elements of `Sym2 (Fin m)`, i.e. the possible edges. -/
noncomputable def pairs (m : ℕ) : Finset (Sym2 (Fin m)) := univ.filter (fun e => ¬ e.IsDiag)

/-- The weight of an edge set `S` in the random graph `G(m, p)`: each possible edge is present
with weight `p` and absent with weight `1 - p`. -/
noncomputable def wt (m : ℕ) (p : ℝ) (S : Finset (Sym2 (Fin m))) : ℝ :=
  (∏ _e ∈ S, p) * ∏ _e ∈ pairs m \ S, (1 - p)

lemma wt_nonneg {m : ℕ} {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (S : Finset (Sym2 (Fin m))) :
    0 ≤ wt m p S :=
  mul_nonneg (prod_nonneg fun _ _ => hp0) (prod_nonneg fun _ _ => by linarith)

lemma sum_wt (m : ℕ) (p : ℝ) : ∑ S ∈ (pairs m).powerset, wt m p S = 1 := by
  have := Finset.prod_add (fun _ => p) (fun _ => 1 - p) (pairs m)
  simp only [add_sub_cancel, prod_const_one] at this
  exact this.symm

lemma sum_wt_subset {m : ℕ} (p : ℝ) {A : Finset (Sym2 (Fin m))} (hA : A ⊆ pairs m) :
    ∑ S ∈ (pairs m).powerset, (if A ⊆ S then wt m p S else 0) = p ^ A.card := by
  have := Finset.prod_add (fun _ => p) (fun e => if e ∈ A then 0 else 1 - p) (pairs m)
  have h1 : ∏ i ∈ pairs m, (p + if i ∈ A then 0 else 1 - p) = p ^ A.card := by
    have : ∀ i, (p + if i ∈ A then (0:ℝ) else 1 - p) = if i ∈ A then p else 1 := by
      intro i; split_ifs <;> ring
    simp only [this]
    rw [prod_ite_mem, inter_eq_right.mpr hA, prod_const]
  rw [h1] at this
  rw [this]
  refine sum_congr rfl fun S hS => ?_
  split_ifs with h
  · unfold wt; congr 1
    refine prod_congr rfl fun e he => ?_
    have : e ∉ A := fun heA => (mem_sdiff.mp he).2 (h heA)
    simp [this]
  · obtain ⟨e, heA, heS⟩ := not_subset.mp h
    rw [prod_eq_zero (i := e) (mem_sdiff.mpr ⟨hA heA, heS⟩) (by simp [heA]), mul_zero]

lemma sum_wt_disjoint {m : ℕ} (p : ℝ) {B : Finset (Sym2 (Fin m))} (hB : B ⊆ pairs m) :
    ∑ S ∈ (pairs m).powerset, (if Disjoint B S then wt m p S else 0) = (1 - p) ^ B.card := by
  have := Finset.prod_add (fun e => if e ∈ B then 0 else p) (fun _ => 1 - p) (pairs m)
  have h1 : ∏ i ∈ pairs m, ((if i ∈ B then 0 else p) + (1 - p)) = (1 - p) ^ B.card := by
    have : ∀ i, ((if i ∈ B then (0:ℝ) else p) + (1 - p)) = if i ∈ B then 1 - p else 1 := by
      intro i; split_ifs <;> ring
    simp only [this]
    rw [prod_ite_mem, inter_eq_right.mpr hB, prod_const]
  rw [h1] at this
  rw [this]
  refine sum_congr rfl fun S hS => ?_
  split_ifs with h
  · unfold wt; congr 1
    refine prod_congr rfl fun e he => ?_
    have : e ∉ B := fun heB => disjoint_left.mp h heB he
    simp [this]
  · obtain ⟨e, heB, heS⟩ := not_disjoint_iff.mp h
    rw [prod_eq_zero (i := e) heS (by simp [heB]), zero_mul]
lemma sum_card_finsetWalkLength {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (n : ℕ) (u : V) :
    ∑ v, #(G.finsetWalkLength n u v) ≤ Fintype.card V ^ n := by
  induction n generalizing u with
  | zero =>
    simp only [finsetWalkLength, pow_zero]
    rw [sum_eq_single u]
    · simp
    · intro b _ hb; simp [Ne.symm hb]
    · simp
  | succ n ih =>
    calc ∑ v, #(G.finsetWalkLength (n + 1) u v)
        ≤ ∑ v, ∑ w : G.neighborSet u, #(G.finsetWalkLength n w v) := by
          refine sum_le_sum fun v _ => ?_
          refine (card_biUnion_le).trans ?_
          simp
      _ = ∑ w : G.neighborSet u, ∑ v, #(G.finsetWalkLength n w v) := sum_comm
      _ ≤ ∑ _w : G.neighborSet u, Fintype.card V ^ n := sum_le_sum fun w _ => ih w
      _ ≤ Fintype.card V ^ (n + 1) := by
          rw [sum_const, card_univ, smul_eq_mul, pow_succ, mul_comm]
          exact Nat.mul_le_mul_left _ (Fintype.card_subtype_le _)

lemma sum_card_closed_walks {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (n : ℕ) :
    ∑ u, #(G.finsetWalkLength (n + 1) u u) ≤ Fintype.card V ^ (n + 1) := by
  calc ∑ u, #(G.finsetWalkLength (n + 1) u u)
      ≤ ∑ u, ∑ w : G.neighborSet u, #(G.finsetWalkLength n w u) := by
        refine sum_le_sum fun v _ => ?_
        refine (card_biUnion_le).trans ?_
        simp
    _ ≤ ∑ u, ∑ w, #(G.finsetWalkLength n w u) := by
        refine sum_le_sum fun u _ => ?_
        exact (sum_map univ (Function.Embedding.subtype _)
          (fun w => #(G.finsetWalkLength n w u))).symm.le.trans
          (sum_le_sum_of_subset (subset_univ _))
    _ = ∑ w, ∑ u, #(G.finsetWalkLength n w u) := sum_comm
    _ ≤ ∑ _w : V, Fintype.card V ^ n := sum_le_sum fun w _ => sum_card_finsetWalkLength G n w
    _ = Fintype.card V ^ (n + 1) := by
        rw [sum_const, card_univ, smul_eq_mul, pow_succ, mul_comm]

open Classical in
/-- Weighted count of the cycles of length at most `g` based at `u` all of whose edges lie in
`S`, counted as closed walks of the complete graph. -/
noncomputable def cyc (m g : ℕ) (S : Finset (Sym2 (Fin m))) (u : Fin m) : ℝ :=
  ∑ ℓ ∈ range (g + 1), ∑ c ∈ (⊤ : SimpleGraph (Fin m)).finsetWalkLength ℓ u u,
    if c.IsCycle ∧ c.edges.toFinset ⊆ S then 1 else 0

lemma edges_toFinset_subset_pairs {m : ℕ} {u v : Fin m} (c : (⊤ : SimpleGraph (Fin m)).Walk u v) :
    c.edges.toFinset ⊆ pairs m := by
  intro e he
  simp only [pairs, mem_filter, mem_univ, true_and]
  exact (⊤ : SimpleGraph (Fin m)).not_isDiag_of_mem_edgeSet
    (c.edges_subset_edgeSet (List.mem_toFinset.mp he))

open Classical in
lemma sum_wt_cycle {m : ℕ} (p : ℝ) {u : Fin m} (c : (⊤ : SimpleGraph (Fin m)).Walk u u) :
    ∑ S ∈ (pairs m).powerset, wt m p S * (if c.IsCycle ∧ c.edges.toFinset ⊆ S then 1 else 0)
      = if c.IsCycle then p ^ c.length else 0 := by
  by_cases hc : c.IsCycle
  · simp only [hc, true_and, ite_true, mul_ite, mul_one, mul_zero]
    rw [sum_wt_subset p (edges_toFinset_subset_pairs c), List.toFinset_card_of_nodup hc.edges_nodup,
      Walk.length_edges]
  · simp [hc]

open Classical in
lemma sum_cycle_le {m : ℕ} {p : ℝ} (hp0 : 0 ≤ p) (ℓ : ℕ) :
    ∑ u : Fin m, ∑ c ∈ (⊤ : SimpleGraph (Fin m)).finsetWalkLength ℓ u u,
      (if c.IsCycle then p ^ ℓ else 0) ≤ ((m : ℝ) * p) ^ ℓ := by
  cases ℓ with
  | zero =>
    rw [sum_eq_zero]
    · positivity
    intro u _
    refine sum_eq_zero fun c hc => ?_
    rw [ite_eq_right_iff]
    intro hcyc
    have := hcyc.three_le_length
    rw [mem_finsetWalkLength_iff.mp hc] at this
    omega
  | succ n =>
    calc _ ≤ ∑ u : Fin m, ∑ c ∈ (⊤ : SimpleGraph (Fin m)).finsetWalkLength (n + 1) u u,
          p ^ (n + 1) :=
          sum_le_sum fun u _ => sum_le_sum fun c _ => by
            split_ifs <;> first | exact le_rfl | positivity
      _ = (∑ u : Fin m, #((⊤ : SimpleGraph (Fin m)).finsetWalkLength (n + 1) u u) : ℕ)
          * p ^ (n + 1) := by
          simp [sum_mul]
      _ ≤ ((m ^ (n + 1) : ℕ) : ℝ) * p ^ (n + 1) := by
          gcongr
          simpa using sum_card_closed_walks (⊤ : SimpleGraph (Fin m)) n
      _ = ((m : ℝ) * p) ^ (n + 1) := by push_cast; ring

open Classical in
lemma expected_cyc_le {m : ℕ} (g : ℕ) {p : ℝ} (hp0 : 0 ≤ p) :
    ∑ S ∈ (pairs m).powerset, wt m p S * ∑ u, cyc m g S u
      ≤ ∑ ℓ ∈ range (g + 1), ((m : ℝ) * p) ^ ℓ := by
  calc ∑ S ∈ (pairs m).powerset, wt m p S * ∑ u, cyc m g S u
      = ∑ S ∈ (pairs m).powerset, ∑ u, ∑ ℓ ∈ range (g + 1),
          ∑ c ∈ (⊤ : SimpleGraph (Fin m)).finsetWalkLength ℓ u u,
            wt m p S * (if c.IsCycle ∧ c.edges.toFinset ⊆ S then 1 else 0) := by
        simp_rw [cyc, mul_sum]
    _ = ∑ ℓ ∈ range (g + 1), ∑ u, ∑ c ∈ (⊤ : SimpleGraph (Fin m)).finsetWalkLength ℓ u u,
          ∑ S ∈ (pairs m).powerset,
            wt m p S * (if c.IsCycle ∧ c.edges.toFinset ⊆ S then 1 else 0) := by
        refine sum_comm.trans ?_
        refine (sum_congr rfl fun u _ => sum_comm).trans ?_
        refine (sum_congr rfl fun u _ => sum_congr rfl fun ℓ _ => sum_comm).trans ?_
        exact sum_comm
    _ = ∑ ℓ ∈ range (g + 1), ∑ u, ∑ c ∈ (⊤ : SimpleGraph (Fin m)).finsetWalkLength ℓ u u,
          (if c.IsCycle then p ^ ℓ else 0) := by
        refine sum_congr rfl fun ℓ _ => sum_congr rfl fun u _ => sum_congr rfl fun c hc => ?_
        rw [sum_wt_cycle, mem_finsetWalkLength_iff.mp hc]
    _ ≤ _ := sum_le_sum fun ℓ _ => sum_cycle_le hp0 ℓ

/-- The pairs inside a vertex set `T`. -/
noncomputable def edgesIn {m : ℕ} (T : Finset (Fin m)) : Finset (Sym2 (Fin m)) :=
  T.offDiag.image Sym2.mk.uncurry

/-- The number of independent `t`-sets of the graph with edge set `S`. -/
noncomputable def indep (m t : ℕ) (S : Finset (Sym2 (Fin m))) : ℝ :=
  ∑ T ∈ powersetCard t (univ : Finset (Fin m)), if Disjoint (edgesIn T) S then 1 else 0

lemma edgesIn_subset_pairs {m : ℕ} (T : Finset (Fin m)) : edgesIn T ⊆ pairs m := by
  intro e he
  simp only [edgesIn, mem_image, mem_offDiag] at he
  obtain ⟨⟨a, b⟩, ⟨-, -, hab⟩, rfl⟩ := he
  simpa [pairs] using hab

lemma expected_indep {m : ℕ} (t : ℕ) (p : ℝ) :
    ∑ S ∈ (pairs m).powerset, wt m p S * indep m t S = m.choose t * (1 - p) ^ t.choose 2 := by
  calc ∑ S ∈ (pairs m).powerset, wt m p S * indep m t S
      = ∑ S ∈ (pairs m).powerset, ∑ T ∈ powersetCard t (univ : Finset (Fin m)),
          (if Disjoint (edgesIn T) S then wt m p S else 0) := by
        simp_rw [indep, mul_sum, mul_ite, mul_one, mul_zero]
    _ = ∑ T ∈ powersetCard t (univ : Finset (Fin m)), ∑ S ∈ (pairs m).powerset,
          (if Disjoint (edgesIn T) S then wt m p S else 0) := sum_comm
    _ = ∑ T ∈ powersetCard t (univ : Finset (Fin m)), (1 - p) ^ t.choose 2 := by
        refine sum_congr rfl fun T hT => ?_
        rw [sum_wt_disjoint p (edgesIn_subset_pairs T), edgesIn, Sym2.card_image_offDiag,
          (mem_powersetCard.mp hT).2]
    _ = m.choose t * (1 - p) ^ t.choose 2 := by
        rw [sum_const, card_powersetCard, card_univ, Fintype.card_fin, nsmul_eq_mul]

/-- The graph with edge set `S`. -/
noncomputable def gr {m : ℕ} (S : Finset (Sym2 (Fin m))) : SimpleGraph (Fin m) :=
  SimpleGraph.fromEdgeSet (S : Set (Sym2 (Fin m)))

lemma disjoint_of_isIndepSet {m : ℕ} {S : Finset (Sym2 (Fin m))} {T : Finset (Fin m)}
    (h : (gr S).IsIndepSet (T : Set (Fin m))) : Disjoint (edgesIn T) S := by
  rw [Finset.disjoint_left]
  intro e he heS
  simp only [edgesIn, mem_image, mem_offDiag] at he
  obtain ⟨⟨a, b⟩, ⟨ha, hb, hab⟩, rfl⟩ := he
  exact h (mem_coe.mpr ha) (mem_coe.mpr hb) hab ((fromEdgeSet_adj _).mpr ⟨heS, hab⟩)

open Classical in
lemma cyc_nonneg {m g : ℕ} (S : Finset (Sym2 (Fin m))) (u : Fin m) : 0 ≤ cyc m g S u :=
  sum_nonneg fun _ _ => sum_nonneg fun _ _ => by split_ifs <;> norm_num

lemma indep_nonneg {m t : ℕ} (S : Finset (Sym2 (Fin m))) : 0 ≤ indep m t S :=
  sum_nonneg fun _ _ => by split_ifs <;> norm_num

open Classical in
lemma one_le_cyc {m g : ℕ} {S : Finset (Sym2 (Fin m))} {u : Fin m} (c : (gr S).Walk u u)
    (hc : c.IsCycle) (hl : c.length ≤ g) : 1 ≤ cyc m g S u := by
  have hE : ∀ e ∈ c.edges, e ∈ (S : Set (Sym2 (Fin m))) ∧ ¬ e.IsDiag := by
    intro e he
    have := c.edges_subset_edgeSet he
    rw [gr, edgeSet_fromEdgeSet] at this
    exact ⟨this.1, this.2⟩
  have hT : ∀ e ∈ c.edges, e ∈ (⊤ : SimpleGraph (Fin m)).edgeSet := by
    intro e he
    rw [edgeSet_top]
    exact (hE e he).2
  set c' := c.transfer ⊤ hT
  have hc' : c'.IsCycle := hc.transfer hT
  have hcond : c'.IsCycle ∧ c'.edges.toFinset ⊆ S := by
    refine ⟨hc', fun e he => ?_⟩
    rw [List.mem_toFinset, Walk.edges_transfer] at he
    exact (hE e he).1
  have hterm : (if c'.IsCycle ∧ c'.edges.toFinset ⊆ S then (1 : ℝ) else 0) = 1 := by
    simp only [hcond, and_self, ite_true]
  calc (1 : ℝ) = if c'.IsCycle ∧ c'.edges.toFinset ⊆ S then (1 : ℝ) else 0 := hterm.symm
    _ ≤ ∑ c ∈ (⊤ : SimpleGraph (Fin m)).finsetWalkLength c.length u u,
          if c.IsCycle ∧ c.edges.toFinset ⊆ S then (1 : ℝ) else 0 := by
        refine single_le_sum (f := fun c : (⊤ : SimpleGraph (Fin m)).Walk u u =>
          if c.IsCycle ∧ c.edges.toFinset ⊆ S then (1 : ℝ) else 0)
          (fun _ _ => by split_ifs <;> norm_num) ?_
        rw [mem_finsetWalkLength_iff, Walk.length_transfer]
    _ ≤ cyc m g S u := by
        refine single_le_sum (f := fun ℓ => ∑ c ∈ (⊤ : SimpleGraph (Fin m)).finsetWalkLength ℓ u u,
          if c.IsCycle ∧ c.edges.toFinset ⊆ S then (1 : ℝ) else 0)
          (fun _ _ => sum_nonneg fun _ _ => by split_ifs <;> norm_num) ?_
        rw [mem_range]; omega

open Classical in
/-- **First-moment step.** If the expected number of short cycles is small compared to `m` and
the expected number of independent `t`-sets is small, some graph on `Fin m` has a set `D` of fewer
than `m / 2` vertices meeting every cycle of length at most `g`, and no independent `t`-set. -/
lemma exists_good_graph (m g t : ℕ) {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hm : 0 < m)
    (h : 2 / m * ∑ ℓ ∈ range (g + 1), ((m : ℝ) * p) ^ ℓ + m.choose t * (1 - p) ^ t.choose 2 < 1) :
    ∃ G : SimpleGraph (Fin m), ∃ D : Finset (Fin m), 2 * D.card < m ∧
      (∀ u (c : G.Walk u u), c.IsCycle → c.length ≤ g → u ∈ D) ∧
      ∀ T : Finset (Fin m), T.card = t → ¬ G.IsIndepSet (T : Set (Fin m)) := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  set Z : Finset (Sym2 (Fin m)) → ℝ := fun S => 2 / m * ∑ u, cyc m g S u + indep m t S with hZ
  have hEZ : ∑ S ∈ (pairs m).powerset, wt m p S * Z S < 1 := by
    calc ∑ S ∈ (pairs m).powerset, wt m p S * Z S
        = 2 / m * ∑ S ∈ (pairs m).powerset, wt m p S * ∑ u, cyc m g S u
          + ∑ S ∈ (pairs m).powerset, wt m p S * indep m t S := by
          rw [mul_sum, ← sum_add_distrib]
          refine sum_congr rfl fun S _ => ?_
          rw [hZ]; ring
      _ ≤ 2 / m * ∑ ℓ ∈ range (g + 1), ((m : ℝ) * p) ^ ℓ + m.choose t * (1 - p) ^ t.choose 2 := by
          rw [expected_indep]
          gcongr
          exact expected_cyc_le g hp0
      _ < 1 := h
  obtain ⟨S, -, hS⟩ : ∃ S ∈ (pairs m).powerset, Z S < 1 := by
    by_contra hcon
    push Not at hcon
    have : ∑ S ∈ (pairs m).powerset, wt m p S * 1 ≤ ∑ S ∈ (pairs m).powerset, wt m p S * Z S :=
      sum_le_sum fun S hS => mul_le_mul_of_nonneg_left (hcon S hS) (wt_nonneg hp0 hp1 S)
    simp only [mul_one, sum_wt] at this
    linarith
  have hcyc0 : 0 ≤ ∑ u, cyc m g S u := sum_nonneg fun u _ => cyc_nonneg S u
  have hind0 := indep_nonneg (t := t) S
  have h2 : 0 ≤ 2 / (m : ℝ) * ∑ u, cyc m g S u := by positivity
  simp only [hZ] at hS
  refine ⟨gr S, univ.filter (fun u => ∃ c : (gr S).Walk u u, c.IsCycle ∧ c.length ≤ g), ?_,
    fun u c hc hl => mem_filter.mpr ⟨mem_univ _, c, hc, hl⟩, fun T hT hTi => ?_⟩
  · have hD : ((univ.filter (fun u => ∃ c : (gr S).Walk u u, c.IsCycle ∧ c.length ≤ g)).card : ℝ)
        ≤ ∑ u, cyc m g S u := by
      rw [card_eq_sum_ones, Nat.cast_sum, Nat.cast_one]
      calc _ ≤ ∑ u ∈ univ.filter (fun u => ∃ c : (gr S).Walk u u, c.IsCycle ∧ c.length ≤ g),
            cyc m g S u := by
            refine sum_le_sum fun u hu => ?_
            obtain ⟨c, hc, hl⟩ := (mem_filter.mp hu).2
            exact one_le_cyc c hc hl
        _ ≤ _ := sum_le_sum_of_subset_of_nonneg (filter_subset _ _)
            fun u _ _ => cyc_nonneg S u
    have : 2 / (m : ℝ) * ∑ u, cyc m g S u < 1 := by linarith
    rw [div_mul_eq_mul_div, div_lt_one hm'] at this
    have h3 : (2 : ℝ) * ((univ.filter
        (fun u => ∃ c : (gr S).Walk u u, c.IsCycle ∧ c.length ≤ g)).card : ℝ) < m := by linarith
    exact_mod_cast h3
  · have : (1 : ℝ) ≤ indep m t S := by
      refine le_trans ?_ (single_le_sum (f := fun T : Finset (Fin m) =>
        if Disjoint (edgesIn T) S then (1 : ℝ) else 0) (fun _ _ => by split_ifs <;> norm_num)
        (mem_powersetCard.mpr ⟨subset_univ T, hT⟩))
      simp [disjoint_of_isIndepSet hTi]
    linarith


/-- **Deletion step.** From a graph on `Fin (2 n)` together with a set `D` of fewer than `n`
vertices meeting every short cycle, and with no independent `t`-set, we get a graph on `Fin n`
of girth greater than `g` all of whose independent sets have fewer than `t` vertices. -/
lemma exists_of_deletion (n g t : ℕ) (G : SimpleGraph (Fin (2 * n))) (D : Finset (Fin (2 * n)))
    (hD : 2 * D.card < 2 * n) (hcyc : ∀ u (c : G.Walk u u), c.IsCycle → c.length ≤ g → u ∈ D)
    (hind : ∀ T : Finset (Fin (2 * n)), T.card = t → ¬ G.IsIndepSet (T : Set (Fin (2 * n)))) :
    ∃ H : SimpleGraph (Fin n), (g : ℕ∞) < H.egirth ∧
      ∀ s : Finset (Fin n), H.IsIndepSet (s : Set (Fin n)) → s.card < t := by
  have hR : n ≤ (univ \ D).card := by
    rw [card_sdiff_of_subset (subset_univ _), card_univ, Fintype.card_fin]; omega
  obtain ⟨R, hRsub, hRcard⟩ := exists_subset_card_eq hR
  set f : Fin n ↪ Fin (2 * n) := (R.orderEmbOfFin hRcard).toEmbedding with hf
  have hfR : ∀ i, f i ∉ D := fun i => by
    have := hRsub (R.orderEmbOfFin_mem hRcard i)
    exact (mem_sdiff.mp this).2
  refine ⟨G.comap f, ?_, fun s hs => ?_⟩
  · rw [← ENat.add_one_le_iff (ENat.natCast_ne_top g), le_egirth]
    intro a w hw
    by_contra hlt
    have hl : w.length ≤ g := by
      have : (w.length : ℕ∞) < g + 1 := lt_of_not_ge hlt
      have h' : w.length < g + 1 := by exact_mod_cast this
      omega
    have hinj : Function.Injective (Embedding.comap f G) := (Embedding.comap f G).injective
    have := hcyc _ (w.map (Embedding.comap f G).toHom) (hw.map hinj)
      (by rw [Walk.length_map]; exact hl)
    exact hfR a this
  · by_contra hst
    push Not at hst
    have hmap : G.IsIndepSet ((s.map f : Finset (Fin (2 * n))) : Set (Fin (2 * n))) := by
      intro x hx y hy hxy hadj
      simp only [coe_map, Set.mem_image, mem_coe] at hx hy
      obtain ⟨a, ha, rfl⟩ := hx
      obtain ⟨b, hb, rfl⟩ := hy
      exact hs ha hb (fun h => hxy (by rw [h])) (by simpa using hadj)
    obtain ⟨T, hTsub, hTcard⟩ := exists_subset_card_eq (s := s.map f) (n := t)
      (by rw [card_map]; exact hst)
    exact hind T hTcard (hmap.mono (by exact_mod_cast hTsub))


lemma bound_cycles (g q : ℕ) (hq : 4 * (g + 1) * (2 ^ (2 * g + 3)) ^ g < q) (m : ℝ)
    (hm1 : (q : ℝ) ^ (2 * g + 3) ≤ m) (hm2 : m ≤ ((q : ℝ) + 1) ^ (2 * g + 3)) :
    2 / m * ∑ ℓ ∈ range (g + 1), (m * (1 / (q : ℝ) ^ (2 * g + 1))) ^ ℓ < 1 / 2 := by
  set K : ℝ := 2 ^ (2 * g + 3) with hK
  have hqR : (4 * (g + 1) * K ^ g : ℝ) < q := by rw [hK]; exact_mod_cast hq
  have hK1 : (1 : ℝ) ≤ K := one_le_pow₀ (by norm_num)
  have hKg : (1 : ℝ) ≤ K ^ g := one_le_pow₀ hK1
  have hq1 : (1 : ℝ) ≤ q := by nlinarith
  have hq0 : (0 : ℝ) < q := by linarith
  have hqpos : (0 : ℝ) < (q : ℝ) ^ (2 * g + 1) := by positivity
  have hm0 : 0 < m := lt_of_lt_of_le (by positivity) hm1
  have hx0 : 0 ≤ m * (1 / (q : ℝ) ^ (2 * g + 1)) := by positivity
  have hx : m * (1 / (q : ℝ) ^ (2 * g + 1)) ≤ K * q ^ 2 := by
    rw [mul_one_div, div_le_iff₀ hqpos]
    calc m ≤ ((q : ℝ) + 1) ^ (2 * g + 3) := hm2
      _ ≤ (2 * q) ^ (2 * g + 3) := by gcongr; linarith
      _ = K * q ^ 2 * q ^ (2 * g + 1) := by rw [hK]; ring
  have hKq : (1 : ℝ) ≤ K * q ^ 2 := by nlinarith
  have hsum : ∑ ℓ ∈ range (g + 1), (m * (1 / (q : ℝ) ^ (2 * g + 1))) ^ ℓ
      ≤ (g + 1) * (K * q ^ 2) ^ g := by
    calc _ ≤ ∑ ℓ ∈ range (g + 1), (K * q ^ 2) ^ g := by
          refine sum_le_sum fun ℓ hℓ => ?_
          exact (pow_le_pow_left₀ hx0 hx ℓ).trans
            (pow_le_pow_right₀ hKq (Nat.lt_succ_iff.mp (mem_range.mp hℓ)))
      _ = (g + 1) * (K * q ^ 2) ^ g := by
          rw [sum_const, card_range, nsmul_eq_mul]; push_cast; ring
  calc 2 / m * ∑ ℓ ∈ range (g + 1), (m * (1 / (q : ℝ) ^ (2 * g + 1))) ^ ℓ
      ≤ 2 / (q : ℝ) ^ (2 * g + 3) * ((g + 1) * (K * q ^ 2) ^ g) := by
        gcongr
      _ = 2 * (g + 1) * K ^ g / (q : ℝ) ^ 3 := by
        field_simp
        ring
      _ ≤ 2 * (g + 1) * K ^ g / q := by
        gcongr
        · exact le_self_pow₀ hq1 (by norm_num)
      _ < 1 / 2 := by
        rw [div_lt_iff₀ hq0]; linarith

lemma two_mul_pow_le_exp (a q : ℕ) (hq : 6 * 2 ^ (a + 3) * (a + 3).factorial ≤ q) :
    2 * ((q : ℝ) + 1) ^ (a + 2) ≤ Real.exp (((q : ℝ) - 1) / 2) := by
  obtain ⟨y, hy⟩ : ∃ y : ℝ, y = ((q : ℝ) + 1) / 2 := ⟨_, rfl⟩
  have hF : (0 : ℝ) < (a + 3).factorial := by exact_mod_cast Nat.factorial_pos _
  have hqR : (6 * 2 ^ (a + 3) * (a + 3).factorial : ℝ) ≤ q := by exact_mod_cast hq
  have hy0 : 0 < y := by rw [hy]; positivity
  have hyb : 3 * 2 ^ (a + 3) * ((a + 3).factorial : ℝ) ≤ y := by rw [hy]; linarith
  have he : Real.exp 1 ≤ 3 := le_of_lt (lt_trans Real.exp_one_lt_d9 (by norm_num))
  have hexp : y ^ (a + 3) / (a + 3).factorial ≤ Real.exp y :=
    Real.pow_div_factorial_le_exp y hy0.le (a + 3)
  have hsplit : Real.exp y = Real.exp 1 * Real.exp (((q : ℝ) - 1) / 2) := by
    rw [← Real.exp_add, hy]; congr 1; ring
  have hq1 : (q : ℝ) + 1 = 2 * y := by rw [hy]; ring
  rw [hq1]
  have hE0 : 0 < Real.exp (((q : ℝ) - 1) / 2) := Real.exp_pos _
  -- 2 (2y)^(a+2) * e * (a+3)! ≤ y^(a+3) ≤ (a+3)! e^y
  have key : 2 * (2 * y) ^ (a + 2) * 3 * (a + 3).factorial ≤ y ^ (a + 3) := by
    have : 2 * (2 * y) ^ (a + 2) * 3 * (a + 3).factorial
        = (3 * 2 ^ (a + 3) * (a + 3).factorial) * y ^ (a + 2) := by ring
    have h3 : y ^ (a + 3) = y * y ^ (a + 2) := by ring
    rw [this, h3]
    exact mul_le_mul_of_nonneg_right hyb (pow_nonneg hy0.le (a + 2))
  rw [div_le_iff₀ hF, hsplit] at hexp
  have h2 : 2 * (2 * y) ^ (a + 2) * Real.exp 1 * (a + 3).factorial
      ≤ 2 * (2 * y) ^ (a + 2) * 3 * (a + 3).factorial := by gcongr
  have := h2.trans (key.trans hexp)
  have hpos : 0 < Real.exp 1 * (a + 3).factorial := by positivity
  nlinarith

lemma bound_indep (a q t : ℕ) (hq : 6 * 2 ^ (a + 3) * (a + 3).factorial ≤ q)
    (ht : t = q ^ (a + 1)) (m : ℝ) (hm0 : 0 ≤ m) (hm2 : m ≤ ((q : ℝ) + 1) ^ (a + 2)) :
    m ^ t * (1 - 1 / (q : ℝ) ^ a) ^ t.choose 2 ≤ 1 / 2 := by
  have hq1n : 1 ≤ q := le_trans (Nat.one_le_iff_ne_zero.mpr (by positivity)) hq
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hq1n
  have hqa : (1 : ℝ) ≤ (q : ℝ) ^ a := one_le_pow₀ hq1
  set p : ℝ := 1 / (q : ℝ) ^ a with hp
  have hp0 : 0 ≤ p := by positivity
  have hp1 : p ≤ 1 := by rw [hp, div_le_one (by positivity)]; exact hqa
  have ht1 : 1 ≤ t := by rw [ht]; exact Nat.one_le_pow _ _ hq1n
  have hexp1 : (1 - p) ^ t.choose 2 ≤ Real.exp (t.choose 2 * -p) := by
    rw [Real.exp_nat_mul]
    exact pow_le_pow_left₀ (by linarith) (by linarith [Real.add_one_le_exp (-p)]) _
  have hpt : (q : ℝ) - 1 ≤ p * ((t : ℝ) - 1) := by
    have : p * ((t : ℝ) - 1) = q - p := by
      rw [hp, ht]; push_cast; field_simp; ring
    rw [this]; linarith
  set b : ℝ := m * Real.exp (-p * ((t : ℝ) - 1) / 2) with hb
  have hb0 : 0 ≤ b := by positivity
  have hbb : b ≤ 1 / 2 := by
    have h2 := two_mul_pow_le_exp a q hq
    calc b ≤ ((q : ℝ) + 1) ^ (a + 2) * Real.exp (-(((q : ℝ) - 1) / 2)) := by
          rw [hb]
          exact mul_le_mul hm2 (Real.exp_le_exp.mpr (by linarith)) (Real.exp_pos _).le
            (by positivity)
      _ ≤ 1 / 2 := by
          rw [Real.exp_neg, ← div_eq_mul_inv, div_le_iff₀ (Real.exp_pos _)]; linarith
  calc m ^ t * (1 - p) ^ t.choose 2 ≤ m ^ t * Real.exp (t.choose 2 * -p) := by gcongr
    _ = b ^ t := by
        rw [hb, mul_pow, ← Real.exp_nat_mul, Nat.cast_choose_two]; congr 2; ring
    _ ≤ (1 / 2) ^ t := pow_le_pow_left₀ hb0 hbb t
    _ ≤ 1 / 2 := pow_le_of_le_one (by norm_num) (by norm_num) (by omega)

lemma exists_root_bracket (E M : ℕ) (hE : E ≠ 0) : ∃ q : ℕ, q ^ E ≤ M ∧ M < (q + 1) ^ E := by
  have hex : ∃ k : ℕ, M < (k + 1) ^ E := ⟨M, lt_of_lt_of_le (Nat.lt_succ_self M)
    (Nat.le_self_pow hE _)⟩
  refine ⟨Nat.find hex, ?_, Nat.find_spec hex⟩
  rcases h : Nat.find hex with _ | j
  · simp [zero_pow hE]
  · have := Nat.find_min hex (m := j) (by omega)
    exact le_of_not_gt this

lemma exists_params (g : ℕ) {ε : ℝ} (hε : 0 < ε) : ∃ N : ℕ, 0 < N ∧ ∀ n ≥ N, ∃ (p : ℝ) (t : ℕ),
    0 ≤ p ∧ p ≤ 1 ∧ (t : ℝ) ≤ ε * n ∧
    2 / ((2 * n : ℕ) : ℝ) * ∑ ℓ ∈ range (g + 1), (((2 * n : ℕ) : ℝ) * p) ^ ℓ
      + ((2 * n).choose t : ℝ) * (1 - p) ^ t.choose 2 < 1 := by
  set Q : ℕ := ⌈2 / ε⌉₊ + 4 * (g + 1) * (2 ^ (2 * g + 3)) ^ g
    + 6 * 2 ^ (2 * g + 1 + 3) * (2 * g + 1 + 3).factorial + 2 with hQ
  have hQ1 : 1 ≤ Q := by omega
  refine ⟨Q ^ (2 * g + 3), Nat.pow_pos hQ1, fun n hn => ?_⟩
  obtain ⟨q, hq1, hq2⟩ := exists_root_bracket (2 * g + 3) (2 * n) (by omega)
  have hqQ : Q ≤ q := by
    by_contra hlt
    have : (q + 1) ^ (2 * g + 3) ≤ Q ^ (2 * g + 3) := Nat.pow_le_pow_left (by omega) _
    omega
  have hqpos : 1 ≤ q := le_trans hQ1 hqQ
  have hq1R : (1 : ℝ) ≤ q := by exact_mod_cast hqpos
  have hqa : (1 : ℝ) ≤ (q : ℝ) ^ (2 * g + 1) := one_le_pow₀ hq1R
  refine ⟨1 / (q : ℝ) ^ (2 * g + 1), q ^ (2 * g + 1 + 1), by positivity,
    by rw [div_le_one (by positivity)]; exact hqa, ?_, ?_⟩
  · have hεq : 2 ≤ ε * q := by
      have h1 : 2 / ε ≤ (q : ℝ) := by
        calc 2 / ε ≤ (⌈2 / ε⌉₊ : ℝ) := Nat.le_ceil _
          _ ≤ q := by exact_mod_cast (by omega : ⌈2 / ε⌉₊ ≤ q)
      rw [div_le_iff₀ hε] at h1; linarith
    have hn2 : ((q : ℝ) ^ (2 * g + 3)) ≤ 2 * n := by exact_mod_cast hq1
    push_cast
    have h3 : (q : ℝ) ^ (2 * g + 3) = q * q ^ (2 * g + 1 + 1) := by ring
    nlinarith [pow_nonneg (Nat.cast_nonneg q : (0 : ℝ) ≤ q) (2 * g + 1 + 1)]
  · have hA := bound_cycles g q (by omega) ((2 * n : ℕ) : ℝ) (by exact_mod_cast hq1)
      (by exact_mod_cast hq2.le)
    have hm2 : ((2 * n : ℕ) : ℝ) ≤ ((q : ℝ) + 1) ^ (2 * g + 1 + 2) := by
      exact_mod_cast hq2.le
    have hB := bound_indep (2 * g + 1) q (q ^ (2 * g + 1 + 1)) (by omega) rfl
      ((2 * n : ℕ) : ℝ) (by positivity) hm2
    have hC : (((2 * n).choose (q ^ (2 * g + 1 + 1)) : ℕ) : ℝ)
        ≤ ((2 * n : ℕ) : ℝ) ^ (q ^ (2 * g + 1 + 1)) := by
      exact_mod_cast Nat.choose_le_pow _ _
    have hp1 : 0 ≤ 1 - 1 / (q : ℝ) ^ (2 * g + 1) := by
      rw [sub_nonneg, div_le_one (by positivity)]; exact hqa
    have := mul_le_mul_of_nonneg_right hC (pow_nonneg hp1 ((q ^ (2 * g + 1 + 1)).choose 2))
    linarith

end ErdosGirth
