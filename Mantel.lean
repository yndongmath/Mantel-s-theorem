import Mathlib
/-
Mantel's thm

1. triangle-free => neighbors of adjacent vertices are disjoint
   => deg(u) + deg(v) ≤ n for every edge {u,v}.

2. double-counting gives ∑ deg(v)^2 ≤ n |E|:
   - ∑_v ∑_{w ∈ N(v)} deg(v) = ∑ deg^2    (each deg(v) counted deg(v) times)
   - ∑_v ∑_{w ∈ N(v)} deg(w) = ∑ deg^2    (swap (v,w) <-> (w,v) by symmetry)
   - adding: ∑_v ∑_{w ∈ N(v)} (deg v + deg w) = 2 ∑ deg^2
   - each ≤ n, so  2 ∑ deg^2 ≤ n · 2|E|

3. Cauchy-Schwarz: (∑ deg)^2 ≤ n ∑ deg^2
   handshaking:     ∑ deg = 2|E|
   combining:       4|E|^2 ≤ n ∑ deg^2 ≤ n^2 |E|
   cancel |E|:      4|E| ≤ n^2
-/

open Finset SimpleGraph Fintype

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

-- part 1
-- any common neighbor of adjacent u,v gives a triangle
lemma disjoint_neighbor (hG : G.CliqueFree 3) {u v : V} (huv : G.Adj u v) :
  Disjoint (G.neighborFinset u) (G.neighborFinset v) := by

  rw [Finset.disjoint_left]
  intro w hwu hwv
  simp [mem_neighborFinset] at hwu hwv

  -- {u, v, w} is a 3-clique
  apply hG {u, v, w}

  constructor
  · -- every pair in {u,v,w} is adjacent
    intro a ha b hb hab
    simp only [mem_coe, mem_insert, mem_singleton] at ha hb
    rcases ha with rfl | rfl | rfl
    · rcases hb with rfl | rfl | rfl
      · contradiction
      · exact huv
      · exact hwu
    · rcases hb with rfl | rfl | rfl
      · exact huv.symm
      · contradiction
      · exact hwv
    · rcases hb with rfl | rfl | rfl
      · exact hwu.symm
      · exact hwv.symm
      · contradiction
  · -- |{u,v,w}| = 3
    rw [card_triple_eq_three_iff]
    exact ⟨huv.ne, hwu.ne, hwv.ne⟩

-- deg(u) + deg(v) ≤ n because N(u) ∪ N(v) ⊆ V and disjoint
lemma deg_add_deg_le (hG : G.CliqueFree 3) {u v : V} (huv : G.Adj u v) :
  G.degree u + G.degree v ≤ card V := by

  have h := disjoint_neighbor hG huv
  calc G.degree u + G.degree v
       = (G.neighborFinset u ∪ G.neighborFinset v).card := (card_union_of_disjoint h).symm
       _ ≤ card V := card_le_univ (G.neighborFinset u ∪ G.neighborFinset v)

-- part 2
-- ∑_v ∑_{w ∈ N(v)} deg(v) = ∑ deg^2
lemma sum_sum_deg_self : ∑ v : V, ∑ _w ∈ G.neighborFinset v,
    G.degree v = ∑ v : V, G.degree v ^ 2 := by
  simp_rw [sum_const, smul_eq_mul, card_neighborFinset]
  congr 1
  ext v
  ring

-- ∑_v ∑_{w ∈ N(v)} deg(w) = ∑ deg^2 (by swapping v,w)
lemma sum_sum_deg_swap :
    ∑ v : V, ∑ w ∈ G.neighborFinset v, G.degree w = ∑ v : V, G.degree v ^ 2 := by
  have h : ∑ v : V, ∑ w ∈ G.neighborFinset v, G.degree w =
           ∑ v : V, ∑ w ∈ G.neighborFinset v, G.degree v := by
    rw [sum_comm]
    refine sum_congr rfl (fun x _ => ?_)
    refine sum_congr ?_ (fun y _ => rfl)
    ext y
    simp [mem_neighborFinset, adj_comm]
  rw [h, sum_sum_deg_self]

-- ∑ deg^2 ≤ n |E|
lemma sum_deg_sq_le (hG : G.CliqueFree 3) : ∑ v : V,
    G.degree v ^ 2 ≤ card V * G.edgeFinset.card := by
  have h_add : 2 * ∑ v : V, G.degree v ^ 2 =
      ∑ v : V, ∑ w ∈ G.neighborFinset v, (G.degree v + G.degree w) := by
    rw [sum_add_distrib]
    simp_rw [← sum_sum_deg_self, ← sum_sum_deg_swap]
    ring

  have h_le : ∑ v : V, ∑ w ∈ G.neighborFinset v, (G.degree v + G.degree w) ≤
      ∑ v : V, ∑ w ∈ G.neighborFinset v, card V := by
    refine sum_le_sum (fun v _ => sum_le_sum (fun w hw => ?_))
    rw [mem_neighborFinset] at hw
    exact deg_add_deg_le hG hw

  have h_bound : ∑ v : V, ∑ _w ∈ G.neighborFinset v, card V =
      card V * (2 * G.edgeFinset.card) := by
    simp_rw [sum_const, smul_eq_mul, card_neighborFinset]
    rw [← mul_sum, sum_degrees_eq_twice_card_edges]

  have h_two : 2 * ∑ v : V, G.degree v ^ 2 ≤ 2 * (card V * G.edgeFinset.card) := by
    calc 2 * ∑ v : V, G.degree v ^ 2
      _ = ∑ v : V, ∑ w ∈ G.neighborFinset v, (G.degree v + G.degree w) := h_add
      _ ≤ ∑ v : V, ∑ w ∈ G.neighborFinset v, card V := h_le
      _ = card V * (2 * G.edgeFinset.card) := h_bound
      _ = 2 * (card V * G.edgeFinset.card) := by ring

  exact Nat.le_of_mul_le_mul_left h_two (by decide)

-- part 3
-- 4|E|^2 ≤ n^2 |E|
lemma four_edges_sq_le (hG : G.CliqueFree 3) :
  4 * G.edgeFinset.card ^ 2 ≤ (card V) ^ 2 * G.edgeFinset.card := by

  -- Cauchy-Schwarz: (∑ deg)^2 ≤ n ∑ deg^2
  have cs : (∑ v ∈ univ, (G.degree v : ℝ)) ^ 2 ≤
      univ.card * ∑ v ∈ univ, (G.degree v : ℝ) ^ 2 :=
      sq_sum_le_card_mul_sum_sq
  rw [card_univ] at cs

  -- ∑ deg^2 ≤ n |E| (from part 2)
  have sq_le : (∑ v : V, (G.degree v : ℝ) ^ 2) ≤
      (card V : ℝ) * (G.edgeFinset.card : ℝ) := by
    exact_mod_cast sum_deg_sq_le hG

  -- handshaking: ∑ deg = 2|E|
  have hs : ∑ v : V, (G.degree v : ℝ) = 2 * (G.edgeFinset.card : ℝ) := by
    exact_mod_cast sum_degrees_eq_twice_card_edges (G := G)

  -- combine: (2|E|)^2 ≤ n^2 |E|, cast back to N
  rw [hs] at cs
  have h : (4 * (G.edgeFinset.card : ℝ) ^ 2) ≤
      ((card V : ℝ) ^ 2 * G.edgeFinset.card) := by nlinarith
  exact_mod_cast h

-- 4|E| ≤ n^2
theorem mantel (hG : G.CliqueFree 3) : 4 * G.edgeFinset.card ≤ (card V) ^ 2 := by
have h4 := four_edges_sq_le hG
  rcases Nat.eq_zero_or_pos G.edgeFinset.card with hE | hE
  · rw [hE, mul_zero]
    exact Nat.zero_le _
  · nlinarith
