import NiceNumbers

/-!
# Certified emptiness of a base

A certificate is a list of consecutive intervals `[a, c)` covering the crude band
`(lo, hi)`.  Each carries the digit lengths `L1`, `L2` of `n^e1`, `n^e2` across it
(checked at the two ends) and one of three reasons nothing in it is nice:

* `tag 0` — the lengths do not add up to `b` (the length identity fails);
* `tag 1` — the top `h` digits of both powers are constant on the interval and
  already repeat a value (`no_pandigital_of_top_clash`);
* `tag 2` — every candidate is checked in full, reading its digits with
  `lowSlots` at the known length, which the kernel can evaluate where `digits`
  (well-founded recursion) cannot.

`checkChain` is a `Bool` the kernel evaluates, and `no_nice_of_cert` is the one
theorem a base needs: everything specific to a base is a single `decide +kernel`.
-/

namespace Nice.Cert

open Nice

structure Ent where
  a : Nat
  c : Nat
  tag : Nat
  L1 : Nat
  L2 : Nat
  h : Nat

/-- Both powers have constant length across `[a, c)`. -/
def lensOK (b e1 e2 : Nat) (x : Ent) : Bool :=
  decide (0 < x.L1) && decide (0 < x.L2)
    && decide (b ^ (x.L1 - 1) ≤ x.a ^ e1) && decide ((x.c - 1) ^ e1 < b ^ x.L1)
    && decide (b ^ (x.L2 - 1) ≤ x.a ^ e2) && decide ((x.c - 1) ^ e2 < b ^ x.L2)

/-- Some value occurs twice in the list (as a negated `allb`, so the §9 lemmas apply). -/
def repeats (b : Nat) (l : List Nat) : Bool :=
  !allb (fun v => decide (occ v l ≤ 1)) (run 0 b)

/-- Full pandigitality of `n`, given the two lengths. -/
def pandL (b e1 e2 L1 L2 n : Nat) : Bool :=
  allb (fun v => decide (occ v (lowSlots b L1 (n ^ e1) ++ lowSlots b L2 (n ^ e2)) = 1))
    (run 0 b)

def checkLeaf (b e1 e2 : Nat) (x : Ent) : Bool :=
  lensOK b e1 e2 x &&
  match x.tag with
  | 0 => decide (x.L1 + x.L2 ≠ b)
  | 1 => decide (x.h ≤ x.L1) && decide (x.h ≤ x.L2)
      && decide (x.a ^ e1 / b ^ (x.L1 - x.h) = (x.c - 1) ^ e1 / b ^ (x.L1 - x.h))
      && decide (x.a ^ e2 / b ^ (x.L2 - x.h) = (x.c - 1) ^ e2 / b ^ (x.L2 - x.h))
      && repeats b (topSlots b x.h x.L1 (x.a ^ e1) ++ topSlots b x.h x.L2 (x.a ^ e2))
  | _ => allb (fun n => !pandL b e1 e2 x.L1 x.L2 n) (run x.a (x.c - x.a))

/-! ### The tree, rebuilt in the kernel

Past a few thousand intervals a certificate cannot be a list literal: the
elaborator's recursion limit stops it near 6 000 entries.  So a `tag 3` entry
names only a length region and a scan width `W`, and the kernel rebuilds the
tree itself.  At each node it tries a top-digit clash at the deepest `h` where
both top quotients agree at the two ends; failing that, it scans the interval
if it is at most `W` wide, and otherwise splits it along multiples of `b^d`
and recurses.  Every node's verdict is a `checkLeaf`, so the soundness proof
never has to know how the tree was built. -/

/-- The largest `h ≤ fuel` at which both top quotients agree at the two ends,
from the four powers at the ends.  Only a heuristic: `checkLeaf` rechecks. -/
def topH (b L1 L2 pa1 pc1 pa2 pc2 : Nat) : Nat → Nat
  | 0 => 0
  | h + 1 =>
    if (pa1 / b ^ (L1 - (h + 1)) == pc1 / b ^ (L1 - (h + 1)))
        && (pa2 / b ^ (L2 - (h + 1)) == pc2 / b ^ (L2 - (h + 1))) then h + 1
    else topH b L1 L2 pa1 pc1 pa2 pc2 h

/-- `f` on each piece of `[a, c)` cut at multiples of `B`, left to right, with at
most `fuel` pieces.  Runs out of fuel as `false`. -/
def splitWith (f : Nat → Nat → Bool) (B : Nat) : Nat → Nat → Nat → Bool
  | 0, a, c => decide (c ≤ a)
  | k + 1, a, c =>
    if c ≤ a then true
    else f a (min c ((a / B + 1) * B)) && splitWith f B k (min c ((a / B + 1) * B)) c

def refute (b e1 e2 L1 L2 W : Nat) : Nat → Nat → Nat → Bool
  | 0, a, c => checkLeaf b e1 e2 ⟨a, c, 2, L1, L2, 0⟩
  | d + 1, a, c =>
    checkLeaf b e1 e2 ⟨a, c, 1, L1, L2,
        topH b L1 L2 (a ^ e1) ((c - 1) ^ e1) (a ^ e2) ((c - 1) ^ e2) (min L1 L2)⟩
      || (if c - a ≤ W then checkLeaf b e1 e2 ⟨a, c, 2, L1, L2, 0⟩
          else splitWith (fun a' c' => refute b e1 e2 L1 L2 W d a' c') (b ^ d) (b + 1) a c)

/-- A certificate entry: `tag 3` is a tree over `[a, c)` with scan width `h`,
at depth `L1`; every other tag is a leaf. -/
def checkEnt (b e1 e2 : Nat) (x : Ent) : Bool :=
  if x.tag = 3 then refute b e1 e2 x.L1 x.L2 x.h x.L1 x.a x.c else checkLeaf b e1 e2 x

/-- The intervals are consecutive from `s` and reach `hi`. -/
def checkChain (b e1 e2 : Nat) : Nat → List Ent → Nat → Bool
  | s, [], hi => decide (hi ≤ s)
  | s, x :: l, hi => decide (x.a = s) && checkEnt b e1 e2 x && checkChain b e1 e2 x.c l hi

theorem exists_of_allb_false {p : Nat → Bool} :
    ∀ l : List Nat, allb p l = false → ∃ v, v ∈ l ∧ p v = false := by
  intro l
  induction l with
  | nil => intro h; simp [allb] at h
  | cons a t ih =>
    intro h
    simp only [allb, Bool.and_eq_false_iff] at h
    rcases h with h | h
    · exact ⟨a, List.mem_cons_self, h⟩
    · obtain ⟨v, hv, hp⟩ := ih h
      exact ⟨v, List.mem_cons_of_mem _ hv, hp⟩

theorem lens_of_lensOK {b e1 e2 : Nat} (hb : 1 < b) {x : Ent} (h : lensOK b e1 e2 x = true)
    {n : Nat} (han : x.a ≤ n) (hnc : n < x.c) :
    numDigits b (n ^ e1) = x.L1 ∧ numDigits b (n ^ e2) = x.L2 := by
  simp only [lensOK, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := h
  constructor
  · exact numDigits_eq_of_len hb h1 (Nat.le_trans h3 (Nat.pow_le_pow_left han _))
      (Nat.lt_of_le_of_lt (Nat.pow_le_pow_left (by omega : n ≤ x.c - 1) _) h4)
  · exact numDigits_eq_of_len hb h2 (Nat.le_trans h5 (Nat.pow_le_pow_left han _))
      (Nat.lt_of_le_of_lt (Nat.pow_le_pow_left (by omega : n ≤ x.c - 1) _) h6)

theorem pandL_of_pandigital {b e1 e2 L1 L2 n : Nat} (hb : 1 < b)
    (hd1 : numDigits b (n ^ e1) = L1) (hd2 : numDigits b (n ^ e2) = L2)
    (hp : Pandigital b e1 e2 n) : pandL b e1 e2 L1 L2 n = true := by
  refine allb_of_mem _ ?_
  intro v hv
  have hvb : v < b := by have := (mem_run b 0 v hv).2; omega
  refine decide_eq_true ?_
  rw [← digits_eq_lowSlots hb L1 _ hd1, ← digits_eq_lowSlots hb L2 _ hd2]
  exact hp v hvb

theorem checkLeaf_sound {b e1 e2 : Nat} (hb : 1 < b) {x : Ent}
    (h : checkLeaf b e1 e2 x = true) {n : Nat} (han : x.a ≤ n) (hnc : n < x.c) :
    ¬ Pandigital b e1 e2 n := by
  intro hp
  simp only [checkLeaf, Bool.and_eq_true] at h
  obtain ⟨hl, ht⟩ := h
  obtain ⟨hd1, hd2⟩ := lens_of_lensOK hb hl han hnc
  split at ht
  · have := pandigital_length hb hp
    simp only [decide_eq_true_eq] at ht
    omega
  · simp only [Bool.and_eq_true, decide_eq_true_eq] at ht
    obtain ⟨⟨⟨⟨hh1, hh2⟩, hq1⟩, hq2⟩, hr⟩ := ht
    simp only [lensOK, Bool.and_eq_true, decide_eq_true_eq] at hl
    obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := hl
    have hf : allb (fun v => decide (occ v (topSlots b x.h x.L1 (x.a ^ e1)
        ++ topSlots b x.h x.L2 (x.a ^ e2)) ≤ 1)) (run 0 b) = false := by
      simpa [repeats] using hr
    obtain ⟨v, -, hv⟩ := exists_of_allb_false _ hf
    have hclash : 2 ≤ occ v (topSlots b x.h x.L1 (x.a ^ e1)
        ++ topSlots b x.h x.L2 (x.a ^ e2)) := by
      simp only [decide_eq_false_iff_not] at hv; omega
    exact no_pandigital_of_top_clash hb h1 h2 h3 h4 h5 h6 hh1 hh2 hq1 hq2 hclash han hnc hp
  · have hm : n ∈ run x.a (x.c - x.a) := mem_run_of _ _ _ han (by omega)
    have := allb_mem _ ht n hm
    rw [pandL_of_pandigital hb hd1 hd2 hp] at this
    exact absurd this (by decide)

theorem splitWith_sound {P : Nat → Prop} {f : Nat → Nat → Bool} {B : Nat}
    (hf : ∀ a c, f a c = true → ∀ n, a ≤ n → n < c → ¬ P n) :
    ∀ k a c, splitWith f B k a c = true → ∀ n, a ≤ n → n < c → ¬ P n := by
  intro k
  induction k with
  | zero =>
    intro a c h n h1 h2
    simp only [splitWith, decide_eq_true_eq] at h
    omega
  | succ k ih =>
    intro a c h n h1 h2
    simp only [splitWith] at h
    split at h
    · omega
    · simp only [Bool.and_eq_true] at h
      obtain ⟨hl, hr⟩ := h
      rcases Nat.lt_or_ge n (min c ((a / B + 1) * B)) with hn | hn
      · exact hf _ _ hl n h1 hn
      · exact ih _ _ hr n hn h2

theorem refute_sound {b e1 e2 L1 L2 W : Nat} (hb : 1 < b) :
    ∀ d a c, refute b e1 e2 L1 L2 W d a c = true →
      ∀ n, a ≤ n → n < c → ¬ Pandigital b e1 e2 n := by
  intro d
  induction d with
  | zero =>
    intro a c h n h1 h2
    exact checkLeaf_sound hb h h1 h2
  | succ d ih =>
    intro a c h n h1 h2
    simp only [refute, Bool.or_eq_true] at h
    rcases h with h | h
    · exact checkLeaf_sound hb h h1 h2
    · split at h
      · exact checkLeaf_sound hb h h1 h2
      · exact splitWith_sound (fun a' c' => ih a' c') _ _ _ h n h1 h2

theorem checkEnt_sound {b e1 e2 : Nat} (hb : 1 < b) {x : Ent}
    (h : checkEnt b e1 e2 x = true) {n : Nat} (han : x.a ≤ n) (hnc : n < x.c) :
    ¬ Pandigital b e1 e2 n := by
  simp only [checkEnt] at h
  split at h
  · exact refute_sound hb _ _ _ h n han hnc
  · exact checkLeaf_sound hb h han hnc

theorem checkChain_sound {b e1 e2 : Nat} (hb : 1 < b) :
    ∀ (l : List Ent) (s hi : Nat), checkChain b e1 e2 s l hi = true →
      ∀ n, s ≤ n → n < hi → ¬ Pandigital b e1 e2 n := by
  intro l
  induction l with
  | nil =>
    intro s hi h n h1 h2
    simp only [checkChain, decide_eq_true_eq] at h
    omega
  | cons x l ih =>
    intro s hi h n h1 h2
    simp only [checkChain, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨hs, hx⟩, hl⟩ := h
    rcases Nat.lt_or_ge n x.c with hc | hc
    · exact checkEnt_sound hb hx (by omega) hc
    · exact ih x.c hi hl n hc h2

/-! ### Gluing ranges

A large base is checked in pieces, one module per piece, because the kernel keeps
what it reduces for the life of the process: one declaration over a whole base-20
tree needs tens of gigabytes, while pieces of a few thousand nodes need about one.
Each piece proves `NiceFree` on its range, and the ranges are glued end to end. -/

/-- No `(e1,e2)`-nice number in `[a, c)`. -/
def NiceFree (b e1 e2 a c : Nat) : Prop := ∀ n, a ≤ n → n < c → ¬ Pandigital b e1 e2 n

theorem NiceFree.trans {b e1 e2 a m c : Nat} (h1 : NiceFree b e1 e2 a m)
    (h2 : NiceFree b e1 e2 m c) : NiceFree b e1 e2 a c := by
  intro n ha hc
  rcases Nat.lt_or_ge n m with h | h
  · exact h1 n ha h
  · exact h2 n h hc

theorem NiceFree.of_chain {b e1 e2 : Nat} (hb : 1 < b) {s hi : Nat} (l : List Ent)
    (h : checkChain b e1 e2 s l hi = true) : NiceFree b e1 e2 s hi :=
  checkChain_sound hb l s hi h

/-- The whole crude band free of nice numbers means the base has none. -/
theorem no_nice_of_free {b e1 e2 lo hi : Nat} (hb : 1 < b)
    (hlo : lo ^ (e1 + e2) < b ^ (b - 2)) (hhi : b ^ b ≤ hi ^ (e1 + e2))
    (h : NiceFree b e1 e2 (lo + 1) hi) (n : Nat) : ¬ Pandigital b e1 e2 n := by
  intro hp
  exact h n (pandigital_gt hb hp hlo) (pandigital_lt hb hp hhi) hp

/-- **The base theorem.**  A certificate that checks, over the crude band, proves the
base has no `(e1,e2)`-nice number at all. -/
theorem no_nice_of_cert {b e1 e2 lo hi : Nat} (hb : 1 < b)
    (hlo : lo ^ (e1 + e2) < b ^ (b - 2)) (hhi : b ^ b ≤ hi ^ (e1 + e2))
    (l : List Ent) (hc : checkChain b e1 e2 (lo + 1) l hi = true) (n : Nat) :
    ¬ Pandigital b e1 e2 n := by
  intro hp
  have h1 := pandigital_gt hb hp hlo
  have h2 := pandigital_lt hb hp hhi
  exact checkChain_sound hb l (lo + 1) hi hc n (by omega) h2 hp

end Nice.Cert
