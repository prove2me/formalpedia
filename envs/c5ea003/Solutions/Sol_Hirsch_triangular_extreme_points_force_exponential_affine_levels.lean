-- Prove2me | solution 1 for Hirsch.triangular_extreme_points_force_exponential_affine_levels
-- status  : ACCEPTED   (prove)
-- author  : @jjosh
-- created : 2026-09-16T21:55:33.403174+00:00
-- url     : https://prove2.me/submissions/fd4ebea0-49c5-4ffb-9555-bbc7509ea2fe

import Mathlib

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section

/-- Distinct positive signed displacements occupy two different off-diagonal
ordered level pairs each, regardless of the common nonzero scale's sign. -/
private theorem distinct_displacements_count
    {I : Type*} [Fintype I] (L : Finset ℝ)
    (a b lambda : I → ℝ) (c : ℝ)
    (ha : ∀ i, a i ∈ L) (hb : ∀ i, b i ∈ L)
    (hpos : ∀ i, 0 < lambda i) (hinj : Function.Injective lambda)
    (hc : c ≠ 0) (hdiff : ∀ i, b i - a i = lambda i * c) :
    2 * Fintype.card I ≤ L.card * (L.card - 1) := by
  classical
  let forward : I → ℝ × ℝ := fun i => (a i, b i)
  let backward : I → ℝ × ℝ := fun i => (b i, a i)
  have hneq : ∀ i, a i ≠ b i := by
    intro i he
    have h := hdiff i
    rw [he, sub_self] at h
    exact (mul_ne_zero (ne_of_gt (hpos i)) hc) h.symm
  have hf : Function.Injective forward := by
    intro i j he
    apply hinj
    have h : b i - a i = b j - a j :=
      congrArg (fun z : ℝ × ℝ => z.2 - z.1) he
    rw [hdiff i, hdiff j] at h
    have hz : (lambda i - lambda j) * c = 0 := by
      rw [sub_mul, h, sub_self]
    exact sub_eq_zero.mp ((mul_eq_zero.mp hz).resolve_right hc)
  have hr : Function.Injective backward := by
    intro i j he
    apply hf
    exact congrArg Prod.swap he
  let F := Finset.univ.image forward
  let B := Finset.univ.image backward
  have hdis : Disjoint F B := by
    apply Finset.disjoint_left.mpr
    intro z hzF hzB
    obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hzF
    obtain ⟨j, _, hj⟩ := Finset.mem_image.mp hzB
    have he : (a i, b i) = (b j, a j) := hi.trans hj.symm
    have h1 : a i = b j := congrArg Prod.fst he
    have h2 : b i = a j := congrArg Prod.snd he
    have hi' := hdiff i
    have hj' := hdiff j
    have hz : (lambda i + lambda j) * c = 0 := by
      rw [add_mul]
      linarith
    exact (mul_ne_zero (ne_of_gt (add_pos (hpos i) (hpos j))) hc) hz
  have hsub : F ∪ B ⊆ L.offDiag := by
    intro z hz
    rcases Finset.mem_union.mp hz with hF | hB
    · obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hF
      exact Finset.mem_offDiag.mpr ⟨ha i, hb i, hneq i⟩
    · obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hB
      exact Finset.mem_offDiag.mpr ⟨hb i, ha i, Ne.symm (hneq i)⟩
  have hFcard : F.card = Fintype.card I := by
    exact (Finset.card_image_of_injective Finset.univ hf).trans (Finset.card_univ)
  have hBcard : B.card = Fintype.card I := by
    exact (Finset.card_image_of_injective Finset.univ hr).trans (Finset.card_univ)
  have hcount : 2 * Fintype.card I ≤ L.offDiag.card := by
    calc
      2 * Fintype.card I = F.card + B.card := by rw [hFcard, hBcard]; omega
      _ = (F ∪ B).card := (Finset.card_union_of_disjoint hdis).symm
      _ ≤ L.offDiag.card := Finset.card_le_card hsub
  simpa only [Finset.offDiag_card, Nat.mul_sub_left_distrib, Nat.mul_one] using hcount

/-- A finite family of distinct positive parallel displacements forces many
coordinate levels in every injective affine embedding. Injectivity supplies
the detecting coordinate; its existence is not an extra hypothesis. -/
theorem accepted_parallel_displacements
    {E I : Type*} [AddCommGroup E] [Module ℝ E] [Fintype I]
    (V : Finset E) (p q : I → E) (g : E) (lambda : I → ℝ)
    (hp : ∀ i, p i ∈ V) (hq : ∀ i, q i ∈ V)
    (hg : g ≠ 0) (hpos : ∀ i, 0 < lambda i)
    (hinj : Function.Injective lambda)
    (hdisp : ∀ i, q i - p i = lambda i • g)
    (r : ℕ) (T : E →ₗ[ℝ] (Fin r → ℝ))
    (hT : Function.Injective T) (offset : Fin r → ℝ) :
    ∃ j : Fin r, (T g) j ≠ 0 ∧
      2 * Fintype.card I ≤
        (V.image (fun x => (T x) j + offset j)).card *
          ((V.image (fun x => (T x) j + offset j)).card - 1) := by
  classical
  have hex : ∃ j : Fin r, (T g) j ≠ 0 := by
    by_contra hn
    have hzero : T g = 0 := by
      funext j
      by_contra hj
      exact hn ⟨j, hj⟩
    exact hg (hT (hzero.trans T.map_zero.symm))
  obtain ⟨j, hj⟩ := hex
  let f : E → ℝ := fun x => (T x) j + offset j
  let L : Finset ℝ := V.image f
  have ha : ∀ i, f (p i) ∈ L := fun i => Finset.mem_image.mpr ⟨p i, hp i, rfl⟩
  have hb : ∀ i, f (q i) ∈ L := fun i => Finset.mem_image.mpr ⟨q i, hq i, rfl⟩
  have hdiff : ∀ i, f (q i) - f (p i) = lambda i * (T g) j := by
    intro i
    calc
      f (q i) - f (p i) = (T (q i - p i)) j := by
        simp only [f, map_sub, Pi.sub_apply]
        ring
      _ = (T (lambda i • g)) j := by rw [hdisp i]
      _ = lambda i * (T g) j := by
        simp only [map_smul, Pi.smul_apply, smul_eq_mul]
  exact ⟨j, hj, distinct_displacements_count L (fun i => f (p i))
    (fun i => f (q i)) lambda ((T g) j) ha hb hpos hinj hj hdiff⟩

#print axioms distinct_displacements_count
#print axioms accepted_parallel_displacements

/-! The preceding proof is the ACCEPTED #279 source, unchanged except the root
name. New work constructs the actual triangular extreme-point family. -/

set_option maxHeartbeats 2000000

namespace TriangularFamily

def tail {n : ℕ} {α : Type*} (x : Fin (n+1) → α) : Fin n → α :=
  fun i => x i.succ

def lead : (n : ℕ) → (Fin n → ℝ) → ℝ
  | 0, _ => 0
  | _+1, x => x 0

def branch (e : ℝ) (b : Bool) (x : ℝ) : ℝ :=
  if b then 1-e*x else e*x

def level (e : ℝ) : (n : ℕ) → (Fin n → Bool) → ℝ
  | 0, _ => 0
  | n+1, b => branch e (b 0) (level e n (tail b))

def point (e : ℝ) : (n : ℕ) → (Fin n → Bool) → (Fin n → ℝ)
  | 0, _ => fun i => Fin.elim0 i
  | n+1, b => Fin.cons (level e (n+1) b) (point e n (tail b))

def Feasible (e : ℝ) {n : ℕ} (x : Fin n → ℝ) : Prop :=
  (∀ i, 0 ≤ x i ∧ x i ≤ 1) ∧
    ∀ (i j : Fin n), i.val+1 = j.val → e*x j ≤ x i ∧ x i ≤ 1-e*x j

private theorem branch_interval (e x : ℝ) (b : Bool)
    (he : 0 < e) (he2 : e < 1/2) (hx : 0 ≤ x ∧ x ≤ 1) :
    e*x ≤ branch e b x ∧ branch e b x ≤ 1-e*x := by
  have hle : e*x ≤ e := by nlinarith [mul_nonneg he.le (sub_nonneg.mpr hx.2)]
  cases b <;> simp [branch] <;> linarith

private theorem level_bounds (e : ℝ) (he : 0 < e) (he2 : e < 1/2) :
    ∀ n (b : Fin n → Bool), 0 ≤ level e n b ∧ level e n b ≤ 1 := by
  intro n
  induction n with
  | zero => intro b; simp [level]
  | succ n ih =>
    intro b
    have hb := ih (tail b)
    have hz := mul_nonneg he.le hb.1
    have hi := branch_interval e (level e n (tail b)) (b 0) he he2 hb
    change 0 ≤ branch e (b 0) (level e n (tail b)) ∧
      branch e (b 0) (level e n (tail b)) ≤ 1
    constructor <;> linarith

private theorem level_injective (e : ℝ) (he : 0 < e) (he2 : e < 1/2) :
    ∀ n, Function.Injective (level e n) := by
  intro n
  induction n with
  | zero =>
    intro a b _
    funext i
    exact Fin.elim0 i
  | succ n ih =>
    intro a b hab
    have ha := level_bounds e he he2 n (tail a)
    have hb := level_bounds e he he2 n (tail b)
    have hla : e*level e n (tail a) ≤ e :=
      (mul_le_mul_of_nonneg_left ha.2 he.le).trans_eq (mul_one e)
    have hlb : e*level e n (tail b) ≤ e :=
      (mul_le_mul_of_nonneg_left hb.2 he.le).trans_eq (mul_one e)
    have hhead : a 0 = b 0 := by
      cases h0 : a 0 <;> cases h1 : b 0
      · rfl
      · simp [level, branch, h0, h1] at hab
        linarith
      · simp [level, branch, h0, h1] at hab
        linarith
      · rfl
    have hprod : e*level e n (tail a) = e*level e n (tail b) := by
      change branch e (a 0) (level e n (tail a)) =
        branch e (b 0) (level e n (tail b)) at hab
      rw [hhead] at hab
      cases h0 : b 0 <;> simp [branch, h0, ne_of_gt he] at hab <;>
        exact congrArg (fun t : ℝ => e*t) hab
    have ht : tail a = tail b := ih (mul_left_cancel₀ (ne_of_gt he) hprod)
    funext i
    exact Fin.cases hhead (fun j => congrFun ht j) i

private theorem lead_point (e : ℝ) (n : ℕ) (b : Fin n → Bool) :
    lead n (point e n b) = level e n b := by
  cases n <;> rfl

private theorem point_injective (e : ℝ) (he : 0 < e) (he2 : e < 1/2)
    (n : ℕ) : Function.Injective (point e n) := by
  intro a b hab
  apply level_injective e he he2 n
  simpa only [lead_point] using congrArg (lead n) hab

private theorem tail_feasible {e : ℝ} {n : ℕ} {x : Fin (n+1) → ℝ}
    (hx : Feasible e x) : Feasible e (tail x) := by
  refine ⟨fun i => hx.1 i.succ, ?_⟩
  intro i j hij
  exact hx.2 i.succ j.succ (by simp only [Fin.val_succ]; omega)

private theorem head_interval {e : ℝ} {n : ℕ} {x : Fin (n+1) → ℝ}
    (hx : Feasible e x) :
    e*lead n (tail x) ≤ x 0 ∧ x 0 ≤ 1-e*lead n (tail x) := by
  cases n with
  | zero => simpa only [lead, mul_zero, sub_zero] using hx.1 0
  | succ n => exact hx.2 0 (0 : Fin (n+1)).succ (by rfl)

private theorem point_feasible (e : ℝ) (he : 0 < e) (he2 : e < 1/2) :
    ∀ n (b : Fin n → Bool), Feasible e (point e n b) := by
  intro n
  induction n with
  | zero =>
    intro b
    exact ⟨fun i => Fin.elim0 i, fun i => Fin.elim0 i⟩
  | succ n ih =>
    intro b
    have ht := ih (tail b)
    constructor
    · intro i
      exact Fin.cases (level_bounds e he he2 (n+1) b) (fun j => ht.1 j) i
    · intro i j hij
      cases i using Fin.cases with
      | zero =>
        cases n with
        | zero => have hj := j.isLt; simp only [Fin.val_zero] at hij; omega
        | succ n =>
          have hj : j = (0 : Fin (n+1)).succ := by
            apply Fin.ext
            simpa only [Fin.val_zero, Fin.val_succ, zero_add] using hij.symm
          subst j
          exact branch_interval e (level e (n+1) (tail b)) (b 0) he he2
            (level_bounds e he he2 (n+1) (tail b))
      | succ i =>
        cases j using Fin.cases with
        | zero => simp only [Fin.val_zero, Fin.val_succ] at hij; omega
        | succ j => exact ht.2 i j (by simp only [Fin.val_succ] at hij; omega)

private theorem endpoint_combo (lo hi x y z a b : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hab : a+b=1)
    (hx : lo ≤ x ∧ x ≤ hi) (hy : lo ≤ y ∧ y ≤ hi)
    (hz : z=lo ∨ z=hi) (heq : a*x+b*y=z) : x=z ∧ y=z := by
  rcases hz with h | h
  · rw [h] at heq ⊢
    have h1 := mul_nonneg ha.le (sub_nonneg.mpr hx.1)
    have h2 := mul_nonneg hb.le (sub_nonneg.mpr hy.1)
    have hs : a*(x-lo)+b*(y-lo)=0 := by
      calc
        a*(x-lo)+b*(y-lo) = (a*x+b*y)-(a+b)*lo := by ring
        _ = 0 := by rw [heq, hab]; ring
    have hax : a*(x-lo)=0 := by linarith
    have hby : b*(y-lo)=0 := by linarith
    exact ⟨sub_eq_zero.mp ((mul_eq_zero.mp hax).resolve_left (ne_of_gt ha)),
      sub_eq_zero.mp ((mul_eq_zero.mp hby).resolve_left (ne_of_gt hb))⟩
  · rw [h] at heq ⊢
    have h1 := mul_nonneg ha.le (sub_nonneg.mpr hx.2)
    have h2 := mul_nonneg hb.le (sub_nonneg.mpr hy.2)
    have hs : a*(hi-x)+b*(hi-y)=0 := by
      calc
        a*(hi-x)+b*(hi-y) = (a+b)*hi-(a*x+b*y) := by ring
        _ = 0 := by rw [heq, hab]; ring
    have hax : a*(hi-x)=0 := by linarith
    have hby : b*(hi-y)=0 := by linarith
    exact ⟨(sub_eq_zero.mp ((mul_eq_zero.mp hax).resolve_left (ne_of_gt ha))).symm,
      (sub_eq_zero.mp ((mul_eq_zero.mp hby).resolve_left (ne_of_gt hb))).symm⟩

private theorem point_combo (e : ℝ) :
    ∀ n (bits : Fin n → Bool) (y z : Fin n → ℝ) (a b : ℝ),
      0 < a → 0 < b → a+b=1 → Feasible e y → Feasible e z →
      a • y + b • z = point e n bits →
      y = point e n bits ∧ z = point e n bits := by
  intro n
  induction n with
  | zero =>
    intro bits y z a b _ _ _ _ _ _
    constructor <;> funext i <;> exact Fin.elim0 i
  | succ n ih =>
    intro bits y z a b ha hb hab hy hz heq
    have htail : a • tail y + b • tail z = point e n (tail bits) := by
      funext i
      exact congrFun heq i.succ
    have ht := ih (tail bits) (tail y) (tail z) a b ha hb hab
      (tail_feasible hy) (tail_feasible hz) htail
    have hy0 := head_interval hy
    have hz0 := head_interval hz
    rw [ht.1] at hy0
    rw [ht.2] at hz0
    have hend : (point e (n+1) bits) 0 = e*lead n (point e n (tail bits)) ∨
        (point e (n+1) bits) 0 = 1-e*lead n (point e n (tail bits)) := by
      simp only [lead_point]
      change branch e (bits 0) (level e n (tail bits)) = e*level e n (tail bits) ∨
        branch e (bits 0) (level e n (tail bits)) = 1-e*level e n (tail bits)
      cases h : bits 0 <;> simp [branch, h]
    have h0 : a*y 0+b*z 0 = (point e (n+1) bits) 0 := congrFun heq 0
    have hh := endpoint_combo _ _ _ _ _ _ _ ha hb hab hy0 hz0 hend h0
    constructor
    · funext i
      exact Fin.cases hh.1 (fun j => congrFun ht.1 j) i
    · funext i
      exact Fin.cases hh.2 (fun j => congrFun ht.2 j) i

private theorem point_extreme (e : ℝ) (he : 0 < e) (he2 : e < 1/2)
    (n : ℕ) (bits : Fin n → Bool) :
    point e n bits ∈ ({x | Feasible e x} : Set (Fin n → ℝ)).extremePoints ℝ := by
  refine ⟨point_feasible e he he2 n bits, ?_⟩
  intro y hy z hz hseg
  obtain ⟨a,b,ha,hb,hab,heq⟩ := hseg
  exact (point_combo e n bits y z a b ha hb hab hy hz heq).1

end TriangularFamily

/-- Actual triangular extreme points, not an assumed exponential displacement
family, force exponentially many levels in every injective affine embedding. -/
theorem solution (e : ℝ) (he : 0 < e) (he2 : e < 1/2) (n : ℕ) :
    ∃ V : Finset (Fin (n+1) → ℝ), V.card = 2^(n+1) ∧
      (∀ x ∈ V, x ∈
        ({y : Fin (n+1) → ℝ |
          (∀ i, 0 ≤ y i ∧ y i ≤ 1) ∧
          ∀ (i j : Fin (n+1)), i.val+1 = j.val → e*y j ≤ y i ∧ y i ≤ 1-e*y j}).extremePoints ℝ) ∧
      ∀ (r : ℕ) (T : (Fin (n+1) → ℝ) →ₗ[ℝ] (Fin r → ℝ)),
        Function.Injective T → ∀ offset : Fin r → ℝ,
          ∃ j : Fin r, 2^(n+1) ≤
            (V.image (fun x => (T x) j + offset j)).card *
              ((V.image (fun x => (T x) j + offset j)).card - 1) := by
  classical
  let V : Finset (Fin (n+1) → ℝ) := Finset.univ.image (TriangularFamily.point e (n+1))
  have hcard : V.card = 2^(n+1) := by
    dsimp [V]
    rw [Finset.card_image_of_injective _ (TriangularFamily.point_injective e he he2 (n+1))]
    simp
  refine ⟨V, hcard, ?_, ?_⟩
  · intro x hx
    obtain ⟨bits, _, rfl⟩ := Finset.mem_image.mp hx
    exact TriangularFamily.point_extreme e he he2 (n+1) bits
  · intro r T hT offset
    let p : (Fin n → Bool) → (Fin (n+1) → ℝ) :=
      fun bits => TriangularFamily.point e (n+1) (Fin.cons false bits)
    let q : (Fin n → Bool) → (Fin (n+1) → ℝ) :=
      fun bits => TriangularFamily.point e (n+1) (Fin.cons true bits)
    let g : Fin (n+1) → ℝ := Fin.cons 1 (fun _ => 0)
    let lam : (Fin n → Bool) → ℝ := fun bits => 1-2*e*TriangularFamily.level e n bits
    have hp : ∀ bits, p bits ∈ V := fun bits =>
      Finset.mem_image.mpr ⟨Fin.cons false bits, Finset.mem_univ _, rfl⟩
    have hq : ∀ bits, q bits ∈ V := fun bits =>
      Finset.mem_image.mpr ⟨Fin.cons true bits, Finset.mem_univ _, rfl⟩
    have hg : g ≠ 0 := by
      intro hz
      have h := congrFun hz 0
      change (1 : ℝ) = 0 at h
      norm_num at h
    have hpos : ∀ bits, 0 < lam bits := by
      intro bits
      have hb := TriangularFamily.level_bounds e he he2 n bits
      have hm := mul_le_mul_of_nonneg_left hb.2 he.le
      dsimp [lam]
      nlinarith
    have hinj : Function.Injective lam := by
      intro a b hab
      apply TriangularFamily.level_injective e he he2 n
      have hm : e*TriangularFamily.level e n a = e*TriangularFamily.level e n b := by
        dsimp [lam] at hab
        linarith
      exact mul_left_cancel₀ (ne_of_gt he) hm
    have hdisp : ∀ bits, q bits-p bits = lam bits • g := by
      intro bits
      funext i
      refine Fin.cases ?_ (fun j => ?_) i
      · change (1-e*TriangularFamily.level e n bits)-e*TriangularFamily.level e n bits =
          (1-2*e*TriangularFamily.level e n bits)*1
        ring
      · change TriangularFamily.point e n bits j-TriangularFamily.point e n bits j =
          lam bits*0
        simp
    obtain ⟨j,_,hcount⟩ := accepted_parallel_displacements V p q g lam
      hp hq hg hpos hinj hdisp r T hT offset
    refine ⟨j, ?_⟩
    have hI : Fintype.card (Fin n → Bool) = 2^n := by simp
    rw [hI] at hcount
    simpa only [pow_succ, Nat.mul_comm] using hcount

#print axioms TriangularFamily.level_injective
#print axioms TriangularFamily.point_extreme
#print axioms solution
