import Mathlib.Data.Fintype.Fin
import Mathlib.Data.Fintype.Pi
import Mathlib.Order.Monotone.Defs

namespace PEqualNP.Outside.L_meta_18465

abbrev Input := Fin 9 → Bool

def decode (m : ℕ) (i : Fin 9) : Bool := m.testBit (i.val + 1)

def edges : List (Fin 9 × Fin 9) :=
  [(0,1),(1,2),(2,3),(0,5),(1,6),(4,6),(2,7),(4,7),(5,7),(3,8),(5,8),(6,8)]

def edge (x : Input) : Bool := edges.any fun e => x e.1 && x e.2

def target (x : Input) : Bool := x 0 || x 3 || x 4 || edge x

def tripleA (x : Input) : Bool := x 2 && x 5 && x 6
def tripleB (x : Input) : Bool := x 1 && x 7 && x 8

def positive : List ℕ := [3,6,12,17,24,33,66,132,160,264,288,320,528,576,640]
def negative : List ℕ := [50,69,104,116,138,201,208,276,385,402,521,548,554,770,773]
def off : List ℕ := [50,104,116,138,208,276,402,548,554,770]

def below (x y : Input) : Bool := (List.finRange 9).all fun i => !x i || y i

lemma belowValid {x y : Input} (h : below x y = true) : x ≤ y := by
  intro i
  have h' := List.all_eq_true.mp h i (List.mem_finRange i)
  change (!x i || y i) = true at h'
  cases hx : x i <;> cases hy : y i <;> simp [hx,hy] at h' ⊢

def lower (L : List ℕ) (x : Input) : Bool := L.any fun m => below (decode m) x
def upper (L : List ℕ) (x : Input) : Bool := L.any fun m => below x (decode m)

lemma lowerWitness {L : List ℕ} {x : Input} (h : lower L x = true) :
    ∃ m ∈ L, decode m ≤ x := by
  obtain ⟨m,hm,q⟩ := List.any_eq_true.mp h
  exact ⟨m,hm,belowValid q⟩

lemma upperWitness {L : List ℕ} {x : Input} (h : upper L x = true) :
    ∃ m ∈ L, x ≤ decode m := by
  obtain ⟨m,hm,q⟩ := List.any_eq_true.mp h
  exact ⟨m,hm,belowValid q⟩

def same (x y : Input) : Bool := below x y && below y x

lemma sameValid {x y : Input} (h : same x y = true) : x = y := by
  unfold same at h
  rw [Bool.and_eq_true] at h
  exact le_antisymm (belowValid h.1) (belowValid h.2)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
lemma targetPositive : ∀ x : Input, target x = true → lower positive x = true := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
lemma targetNegative : ∀ x : Input, target x = false →
    upper (negative.filter fun m => m.testBit 0) x = true := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
lemma edgeNegative : ∀ x : Input, edge x = false → upper negative x = true := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
lemma edgePositive : ∀ x : Input, edge x = true →
    lower (positive.filter fun m => !m.testBit 0) x = true := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
lemma edgeExceptions : ∀ x : Input, edge x = false →
    ((upper off x || same x (decode 200)) || same x (decode 772)) = true := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
lemma lowerA : ∀ x : Input, tripleA x = true → below (decode 200) x = true := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
lemma lowerB : ∀ x : Input, tripleB x = true → below (decode 772) x = true := by
  decide +kernel

lemma trueAbove {a b : Bool} (h : a ≤ b) (t : a = true) : b = true := by
  cases a <;> cases b <;> simp_all
  exact (show ¬ ((true : Bool) ≤ false) by decide) h

lemma falseBelow {a b : Bool} (h : a ≤ b) (t : b = false) : a = false := by
  cases a <;> cases b <;> simp_all
  exact (show ¬ ((true : Bool) ≤ false) by decide) h

def select (f g h : Input → Bool) (m : ℕ) : Bool :=
  bif m.testBit 0 || h (decode m) then g (decode m) else f (decode m)

lemma solve (f g h : Input → Bool) (mf : Monotone f) (mg : Monotone g) (mh : Monotone h)
    (fg : ∀ x, f x ≤ g x) (zeroH : ∀ m ∈ off, h (decode m) = false)
    (pos : ∀ m ∈ positive, select f g h m = true)
    (neg : ∀ m ∈ negative, select f g h m = false) (x : Input) :
    g x = target x ∧ (f x = true → edge x = true) ∧
      (f x || h x) = (edge x || h (decode 200) && tripleA x || h (decode 772) && tripleB x) := by
  have fOff (no : edge x = false) : f x = false := by
    obtain ⟨m,hm,le⟩ := upperWitness (edgeNegative x no)
    have kn : f (decode m) = false := by
      have row := neg m hm
      unfold select at row
      cases cs : (m.testBit 0 || h (decode m)) with
      | false => rw [cs] at row; exact row
      | true => rw [cs] at row; exact falseBelow (fg _) row
    exact falseBelow (mf le) kn
  refine ⟨?_, ?_, ?_⟩
  · cases ct : target x with
    | false =>
      obtain ⟨m,hm,le⟩ := upperWitness (targetNegative x ct)
      obtain ⟨hm,bit⟩ := List.mem_filter.mp hm
      exact falseBelow (mg le) (by simpa [select,bit] using neg m hm)
    | true =>
      obtain ⟨m,hm,le⟩ := lowerWitness (targetPositive x ct)
      have kn : g (decode m) = true := by
        have row := pos m hm
        unfold select at row
        cases cs : (m.testBit 0 || h (decode m)) with
        | false => rw [cs] at row; exact trueAbove (fg _) row
        | true => rw [cs] at row; exact row
      exact trueAbove (mg le) kn
  · intro on
    cases ce : edge x with
    | false => exact (Bool.false_ne_true ((fOff ce).symm.trans on)).elim
    | true => rfl
  · cases ce : edge x with
    | true =>
      obtain ⟨m,hm,le⟩ := lowerWitness (edgePositive x ce)
      obtain ⟨hm,bit⟩ := List.mem_filter.mp hm
      have even : m.testBit 0 = false := by simpa using bit
      have either : (f x || h x) = true := by
        cases hs : h (decode m) with
        | false =>
          have v : f (decode m) = true := by simpa [select,even,hs] using pos m hm
          simp [trueAbove (mf le) v]
        | true => simp [trueAbove (mh le) hs]
      simp [either]
    | false =>
      simp only [fOff ce, Bool.false_or]
      apply Bool.eq_iff_iff.mpr
      constructor
      · intro ht
        have ex := edgeExceptions x ce
        simp only [Bool.or_eq_true] at ex ⊢
        rcases ex with (known | aa) | bb
        · obtain ⟨m,hm,le⟩ := upperWitness known
          exact (Bool.false_ne_true ((falseBelow (mh le) (zeroH m hm)).symm.trans ht)).elim
        · have eq := sameValid aa
          rw [eq] at ht ⊢
          exact Or.inl (by simpa [ht] using (show tripleA (decode 200) = true by decide))
        · have eq := sameValid bb
          rw [eq] at ht ⊢
          exact Or.inr (by simpa [ht] using (show tripleB (decode 772) = true by decide))
      · intro H
        rw [Bool.or_eq_true] at H
        rcases H with ha | hb
        · rw [Bool.and_eq_true] at ha
          obtain ⟨v,t⟩ := ha
          exact trueAbove (mh (belowValid (lowerA x t))) v
        · rw [Bool.and_eq_true] at hb
          obtain ⟨v,t⟩ := hb
          exact trueAbove (mh (belowValid (lowerB x t))) v

end PEqualNP.Outside.L_meta_18465

theorem PEqualNP.Outside.L_meta_18465 :
    ∀ (x1 x2 x3 : (Fin (9 : ℕ) → Bool) → Bool),   Monotone x1 →     Monotone x2 →       Monotone x3 →         (∀ (x7 : Fin (9 : ℕ) → Bool), x1 x7 ≤ x2 x7) →           have x8 : ℕ → Fin (9 : ℕ) → Bool := fun (x8 : ℕ) (x9 : Fin (9 : ℕ)) => x8.testBit (↑x9 + (1 : ℕ));           have x9 : (Fin (9 : ℕ) → Bool) → Bool := fun (x9 : Fin (9 : ℕ) → Bool) => [((0 : Fin (9 : ℕ)), (1 : Fin (9 : ℕ))), ((1 : Fin (9 : ℕ)), (2 : Fin (9 : ℕ))), ((2 : Fin (9 : ℕ)), (3 : Fin (9 : ℕ))), ((0 : Fin (9 : ℕ)), (5 : Fin (9 : ℕ))), ((1 : Fin (9 : ℕ)), (6 : Fin (9 : ℕ))), ((4 : Fin (9 : ℕ)), (6 : Fin (9 : ℕ))), ((2 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))), ((4 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))), ((5 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))), ((3 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))), ((5 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))), ((6 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ)))].any fun (x10 : Fin (9 : ℕ) × Fin (9 : ℕ)) => x9 x10.1 && x9 x10.2;           have x10 : ℕ → Bool := fun (x10 : ℕ) => bif x10.testBit (0 : ℕ) || x3 (x8 x10) then x2 (x8 x10) else x1 (x8 x10);           (∀ x11 ∈ [(50 : ℕ), (104 : ℕ), (116 : ℕ), (138 : ℕ), (208 : ℕ), (276 : ℕ), (402 : ℕ), (548 : ℕ), (554 : ℕ), (770 : ℕ)], x3 (x8 x11) = Bool.false) → (∀ x12 ∈ [(3 : ℕ), (6 : ℕ), (12 : ℕ), (17 : ℕ), (24 : ℕ), (33 : ℕ), (66 : ℕ), (132 : ℕ), (160 : ℕ), (264 : ℕ), (288 : ℕ), (320 : ℕ), (528 : ℕ), (576 : ℕ), (640 : ℕ)], x10 x12 = Bool.true) → (∀ x13 ∈ [(50 : ℕ), (69 : ℕ), (104 : ℕ), (116 : ℕ), (138 : ℕ), (201 : ℕ), (208 : ℕ), (276 : ℕ), (385 : ℕ), (402 : ℕ), (521 : ℕ), (548 : ℕ), (554 : ℕ), (770 : ℕ), (773 : ℕ)], x10 x13 = Bool.false) → ∀ (x14 : Fin (9 : ℕ) → Bool), x2 x14 = (x14 (0 : Fin (9 : ℕ)) || x14 (3 : Fin (9 : ℕ)) || x14 (4 : Fin (9 : ℕ)) || x9 x14) ∧ (x1 x14 = Bool.true → x9 x14 = Bool.true) ∧ (x1 x14 || x3 x14) = (x9 x14 || x3 (x8 (200 : ℕ)) && (x14 (2 : Fin (9 : ℕ)) && x14 (5 : Fin (9 : ℕ)) && x14 (6 : Fin (9 : ℕ))) || x3 (x8 (772 : ℕ)) && (x14 (1 : Fin (9 : ℕ)) && x14 (7 : Fin (9 : ℕ)) && x14 (8 : Fin (9 : ℕ)))) :=
  PEqualNP.Outside.L_meta_18465.solve
