-- Prove2me | solution 2 for Bridges.InfiniteCubicMatchings.bridge_sides_infinite_of_bergeFulkerson
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-20T16:10:06.00185+00:00
-- url     : https://prove2.me/submissions/c7822ecd-b503-4d16-a2c5-a106bcdc38a8

import Mathlib
import Definitions.Def_Bridges_InfiniteCubicMatchings
import Definitions.Def_Bridges_InfiniteCubicMatchingsBridgeParity

open Bridges.InfiniteCubicMatchings in
theorem solution {V : Type*} {G : SimpleGraph V} (hG : IsCubic G) (hBF : BergeFulkerson G)
    {u w : V} (hbr : G.IsBridge s(u, w)) :
    (bridgeSide G u w).Infinite ∧ (bridgeSide G w u).Infinite := by
  classical
  have core : ∀ a b : V, G.IsBridge s(a, b) → (bridgeSide G a b).Finite →
      ¬ BergeFulkerson G := by
    intro u w hbr hfin
    classical
    haveI : DecidableEq V := Classical.decEq V
    -- a fixed-point-free involution on a finite set of pairs forces an even cardinality
    have evenInvolP : ∀ (n : ℕ) (D : Finset (V × V)) (f : V × V → V × V),
        D.card = n → (∀ a ∈ D, f a ∈ D) → (∀ a ∈ D, f (f a) = a) → (∀ a ∈ D, f a ≠ a) →
        Even D.card := by
      intro n
      induction n using Nat.strong_induction_on with
      | _ n ih =>
        intro D f hcard hmap hinv hne
        rcases Finset.eq_empty_or_nonempty D with rfl | ⟨a, ha⟩
        · simp
        · have hfa : f a ∈ D := hmap a ha
          have hane : f a ≠ a := hne a ha
          have hfaE : f a ∈ D.erase a := Finset.mem_erase.2 ⟨hane, hfa⟩
          have hcard' : ((D.erase a).erase (f a)).card + 2 = D.card := by
            have h2 : 1 ≤ (D.erase a).card := Finset.card_pos.2 ⟨f a, hfaE⟩
            rw [Finset.card_erase_of_mem hfaE, Finset.card_erase_of_mem ha]
            rw [Finset.card_erase_of_mem ha] at h2
            have h1 : 1 ≤ D.card := Finset.card_pos.2 ⟨a, ha⟩
            omega
          have hmap' : ∀ b ∈ (D.erase a).erase (f a), f b ∈ (D.erase a).erase (f a) := by
            intro b hb
            obtain ⟨hbfa, hb'⟩ := Finset.mem_erase.1 hb
            obtain ⟨hba, hbD⟩ := Finset.mem_erase.1 hb'
            refine Finset.mem_erase.2 ⟨?_, Finset.mem_erase.2 ⟨?_, hmap b hbD⟩⟩
            · intro hcon
              apply hba
              have hh : f (f b) = f (f a) := by rw [hcon]
              rw [hinv b hbD, hinv a ha] at hh
              exact hh
            · intro hcon
              apply hbfa
              have hh : f (f b) = f a := by rw [hcon]
              rw [hinv b hbD] at hh
              exact hh
          have hlt : ((D.erase a).erase (f a)).card < n := by omega
          have hev := ih _ hlt ((D.erase a).erase (f a)) f rfl hmap'
            (fun b hb => hinv b (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hb)))
            (fun b hb => hne b (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hb)))
          rw [Nat.even_iff] at hev ⊢
          omega
    have evenInvolV : ∀ (n : ℕ) (D : Finset V) (f : V → V),
        D.card = n → (∀ a ∈ D, f a ∈ D) → (∀ a ∈ D, f (f a) = a) → (∀ a ∈ D, f a ≠ a) →
        Even D.card := by
      intro n
      induction n using Nat.strong_induction_on with
      | _ n ih =>
        intro D f hcard hmap hinv hne
        rcases Finset.eq_empty_or_nonempty D with rfl | ⟨a, ha⟩
        · simp
        · have hfa : f a ∈ D := hmap a ha
          have hane : f a ≠ a := hne a ha
          have hfaE : f a ∈ D.erase a := Finset.mem_erase.2 ⟨hane, hfa⟩
          have hcard' : ((D.erase a).erase (f a)).card + 2 = D.card := by
            have h2 : 1 ≤ (D.erase a).card := Finset.card_pos.2 ⟨f a, hfaE⟩
            rw [Finset.card_erase_of_mem hfaE, Finset.card_erase_of_mem ha]
            rw [Finset.card_erase_of_mem ha] at h2
            have h1 : 1 ≤ D.card := Finset.card_pos.2 ⟨a, ha⟩
            omega
          have hmap' : ∀ b ∈ (D.erase a).erase (f a), f b ∈ (D.erase a).erase (f a) := by
            intro b hb
            obtain ⟨hbfa, hb'⟩ := Finset.mem_erase.1 hb
            obtain ⟨hba, hbD⟩ := Finset.mem_erase.1 hb'
            refine Finset.mem_erase.2 ⟨?_, Finset.mem_erase.2 ⟨?_, hmap b hbD⟩⟩
            · intro hcon
              apply hba
              have hh : f (f b) = f (f a) := by rw [hcon]
              rw [hinv b hbD, hinv a ha] at hh
              exact hh
            · intro hcon
              apply hbfa
              have hh : f (f b) = f a := by rw [hcon]
              rw [hinv b hbD] at hh
              exact hh
          have hlt : ((D.erase a).erase (f a)).card < n := by omega
          have hev := ih _ hlt ((D.erase a).erase (f a)) f rfl hmap'
            (fun b hb => hinv b (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hb)))
            (fun b hb => hne b (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hb)))
          rw [Nat.even_iff] at hev ⊢
          omega
    -- basic facts about the bridge
    have hbr' := hbr
    rw [SimpleGraph.isBridge_iff] at hbr'
    obtain ⟨hadj, hunreach⟩ := hbr'
    have huS : u ∈ bridgeSide G u w := SimpleGraph.Reachable.refl u
    have hwS : w ∉ bridgeSide G u w := hunreach
    have hclosure : ∀ v ∈ bridgeSide G u w, ∀ x, G.Adj v x → s(v, x) ≠ s(u, w) →
        x ∈ bridgeSide G u w := by
      intro v hv x hvx hne
      have hstep : (G \ SimpleGraph.fromEdgeSet {s(u, w)}).Adj v x := by
        refine ⟨hvx, ?_⟩
        intro hcon
        rw [SimpleGraph.fromEdgeSet_adj] at hcon
        exact hne (Set.mem_singleton_iff.1 hcon.1)
      have hreach : (G \ SimpleGraph.fromEdgeSet {s(u, w)}).Reachable u v := hv
      exact hreach.trans hstep.reachable
    -- neighbourhoods are finite triples
    have hNfin : ∀ v : V, (G.neighborSet v).Finite := by
      intro v
      by_contra hinf
      have hI : (G.neighborSet v).Infinite := hinf
      have hz := hI.ncard
      rw [hG v] at hz
      omega
    set Sf : Finset V := hfin.toFinset with hSf
    have hSfmem : ∀ v, v ∈ Sf ↔ v ∈ bridgeSide G u w := by
      intro v
      rw [hSf, Set.Finite.mem_toFinset]
    set D : Finset (V × V) :=
      Sf.biUnion (fun v => ((hNfin v).toFinset).image (fun x => (v, x))) with hD
    have hDmem : ∀ p : V × V, p ∈ D ↔ (p.1 ∈ bridgeSide G u w ∧ G.Adj p.1 p.2) := by
      intro p
      rw [hD]
      simp only [Finset.mem_biUnion, Finset.mem_image, Set.Finite.mem_toFinset]
      constructor
      · rintro ⟨v, hv, x, hx, rfl⟩
        exact ⟨(hSfmem v).1 hv, hx⟩
      · rintro ⟨h1, h2⟩
        exact ⟨p.1, (hSfmem p.1).2 h1, p.2, h2, rfl⟩
    have hDcard : D.card = 3 * Sf.card := by
      rw [hD, Finset.card_biUnion]
      · have hterm : ∀ v ∈ Sf, (((hNfin v).toFinset).image (fun x => (v, x))).card = 3 := by
          intro v _
          have hcard3 : ((hNfin v).toFinset).card = 3 := by
            rw [← hG v, Set.ncard_eq_toFinset_card _ (hNfin v)]
          rw [Finset.card_image_of_injective _ (fun a b hab => by simpa using hab), hcard3]
        rw [Finset.sum_congr rfl hterm, Finset.sum_const, smul_eq_mul, mul_comm]
      · intro a _ b _ hab
        refine Finset.disjoint_left.2 ?_
        intro p hp hq
        obtain ⟨x, -, hx⟩ := Finset.mem_image.1 hp
        obtain ⟨y, -, hy⟩ := Finset.mem_image.1 hq
        apply hab
        have h1 : p.1 = a := by rw [← hx]
        have h2 : p.1 = b := by rw [← hy]
        rw [← h1, h2]
    -- the side has odd cardinality
    have hSodd : Odd Sf.card := by
      have hbridgeD : ((u, w) : V × V) ∈ D := (hDmem _).2 ⟨huS, hadj⟩
      have hmap : ∀ p ∈ D.erase (u, w), (p.2, p.1) ∈ D.erase (u, w) := by
        intro p hp
        obtain ⟨hne, hpD⟩ := Finset.mem_erase.1 hp
        obtain ⟨h1, h2⟩ := (hDmem p).1 hpD
        have hp2S : p.2 ∈ bridgeSide G u w := by
          refine hclosure p.1 h1 p.2 h2 ?_
          intro hcon
          rcases Sym2.eq_iff.1 hcon with ⟨h3, h4⟩ | ⟨h3, h4⟩
          · exact hne (by rw [← h3, ← h4])
          · rw [h3] at h1
            exact hwS h1
        refine Finset.mem_erase.2 ⟨?_, (hDmem _).2 ⟨hp2S, h2.symm⟩⟩
        intro hcon
        have h6 : p.1 = w := congrArg Prod.snd hcon
        rw [h6] at h1
        exact hwS h1
      have hinv : ∀ p ∈ D.erase (u, w), ((p.2, p.1).2, (p.2, p.1).1) = p := by
        intro p _
        rfl
      have hnofix : ∀ p ∈ D.erase (u, w), (p.2, p.1) ≠ p := by
        intro p hp hcon
        obtain ⟨-, hpD⟩ := Finset.mem_erase.1 hp
        obtain ⟨-, h2⟩ := (hDmem p).1 hpD
        have hxx : p.2 = p.1 := congrArg Prod.fst hcon
        rw [hxx] at h2
        exact G.irrefl h2
      have heven := evenInvolP (D.erase (u, w)).card (D.erase (u, w))
        (fun p => (p.2, p.1)) rfl hmap hinv hnofix
      rw [Finset.card_erase_of_mem hbridgeD, hDcard] at heven
      have hpos : 1 ≤ 3 * Sf.card := by
        have hc := Finset.card_pos.2 ⟨((u, w) : V × V), hbridgeD⟩
        omega
      rw [Nat.odd_iff]
      rw [Nat.even_iff] at heven
      omega
    -- hence the bridge lies in every perfect matching
    have hbridge_mem : ∀ M : PerfectMatching G, M.partner u = w := by
      intro M
      by_contra hcon
      have hmapS : ∀ v ∈ Sf, M.partner v ∈ Sf := by
        intro v hv
        have hvS : v ∈ bridgeSide G u w := (hSfmem v).1 hv
        refine (hSfmem _).2 (hclosure v hvS (M.partner v) (M.isAdj v) ?_)
        intro hcc
        rcases Sym2.eq_iff.1 hcc with ⟨h3, h4⟩ | ⟨h3, h4⟩
        · exact hcon (by rw [← h3, ← h4])
        · rw [h3] at hvS
          exact hwS hvS
      have heven := evenInvolV Sf.card Sf M.partner rfl hmapS (fun v _ => M.invol v)
        (fun v _ hcc => by
          have hadjv := M.isAdj v
          rw [hcc] at hadjv
          exact G.irrefl hadjv)
      rw [Nat.even_iff] at heven
      rw [Nat.odd_iff] at hSodd
      omega
    rintro ⟨M, hM⟩
    have hmem : ∀ i, s(u, w) ∈ (M i).edges := by
      intro i
      refine ⟨u, ?_⟩
      rw [hbridge_mem (M i)]
    have hedge : s(u, w) ∈ G.edgeSet := hadj
    have hcard := hM s(u, w) hedge
    have hset : {i : Fin 6 | s(u, w) ∈ (M i).edges} = Set.univ := by
      ext i
      simp [hmem i]
    rw [hset, Set.ncard_univ] at hcard
    simp at hcard
  constructor
  · intro hfin
    exact core u w hbr hfin hBF
  · intro hfin
    have hbr' : G.IsBridge s(w, u) := by
      rw [Sym2.eq_swap]
      exact hbr
    exact core w u hbr' hfin hBF
