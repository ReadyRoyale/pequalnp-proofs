import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_18522

abbrev Assignment := Fin 14 → Bool
abbrev left (i : Fin 7) : Fin 14 := Fin.castAdd 7 i
abbrev right (j : Fin 7) : Fin 14 := Fin.natAdd 7 j

abbrev edge (i j : Fin 7) : Prop := i = j ∨ i = j + 1 ∨ i = j + 3

abbrev Independent (x : Assignment) : Prop :=
  ¬ ∃ i j : Fin 7, edge i j ∧ x (left i) = true ∧ x (right j) = true

def allowedRight (a : Fin 7 → Bool) (j : Fin 7) : Bool :=
  decide (∀ i, edge i j → a i = false)

def allowedLeft (b : Fin 7 → Bool) (i : Fin 7) : Bool :=
  decide (∀ j, edge i j → b j = false)

def completion (a : Fin 7 → Bool) : Assignment :=
  fun k => Fin.addCases (m := 7) (n := 7) (motive := fun _ => Bool) a (allowedRight a) k

def masks : List ℕ :=
  [127, 244, 361, 480, 595, 720, 833, 1063, 1188, 1313, 1539, 2126, 2244,
   2376, 2626, 3008, 3078, 4125, 4244, 4361, 4625, 5125, 5889, 6156, 7300,
   8250, 8368, 8488, 8722, 9250, 9632, 10250, 11778, 12312, 12944, 14600,
   16256]

theorem left_ne_right (i j : Fin 7) : left i ≠ right j := by
  intro he
  have h := congrArg Fin.val he
  have hi := i.isLt
  simp only [left, right, Fin.val_castAdd, Fin.val_natAdd] at h
  omega

theorem left_injective : Function.Injective left := by
  intro i j h
  have hv := congrArg (fun k : Fin 14 => k.val) h
  exact Fin.ext hv

theorem right_injective : Function.Injective right := by
  intro i j h
  apply Fin.ext
  have hv := congrArg Fin.val h
  simp only [right, Fin.val_natAdd] at hv
  omega

theorem add_free {x : Assignment} (h : Maximal Independent x) (w : Fin 14)
    (fleft : ∀ i j, edge i j → left i = w → x (right j) = false)
    (fright : ∀ i j, edge i j → right j = w → x (left i) = false) :
    x w = true := by
  let y := Function.update x w true
  have hy : Independent y := by
    rintro ⟨i, j, e, yi, yj⟩
    by_cases hi : left i = w
    · have hj : right j ≠ w := by
        intro hj
        exact left_ne_right i j (hi.trans hj.symm)
      have hval : y (right j) = x (right j) := Function.update_of_ne hj true x
      exact Bool.noConfusion ((fleft i j e hi).symm.trans (hval.symm.trans yj))
    · by_cases hj : right j = w
      · have hval : y (left i) = x (left i) := Function.update_of_ne hi true x
        exact Bool.noConfusion ((fright i j e hj).symm.trans (hval.symm.trans yi))
      · have hleft : y (left i) = x (left i) := Function.update_of_ne hi true x
        have hright : y (right j) = x (right j) := Function.update_of_ne hj true x
        exact h.1 ⟨i, j, e, hleft.symm.trans yi, hright.symm.trans yj⟩
  have hxy : x ≤ y := by
    intro k
    by_cases hk : k = w
    · subst k
      cases x w <;> simp [y]
    · simp [y, hk]
  have hyx : y ≤ x := h.2 hy hxy
  have htrue : true ≤ x w := by simpa only [y, Function.update_self] using hyx w
  cases hbit : x w
  · have impossible : ¬ true ≤ false := by decide
    rw [hbit] at htrue
    exact (impossible htrue).elim
  · rfl

theorem right_forced {x : Assignment} (h : Maximal Independent x) (j : Fin 7) :
    x (right j) = allowedRight (fun i => x (left i)) j := by
  rw [Bool.eq_iff_iff, allowedRight, decide_eq_true_eq]
  constructor
  · intro hj i e
    cases hi : x (left i)
    · rfl
    · exact (h.1 ⟨i, j, e, hi, hj⟩).elim
  · intro free
    apply add_free h (right j)
    · intro i k _ hi
      exact (left_ne_right i j hi).elim
    · intro i k e hk
      have eq : k = j := right_injective hk
      subst k
      exact free i e

theorem left_forced {x : Assignment} (h : Maximal Independent x) (i : Fin 7) :
    x (left i) = allowedLeft (fun j => x (right j)) i := by
  rw [Bool.eq_iff_iff, allowedLeft, decide_eq_true_eq]
  constructor
  · intro hi j e
    cases hj : x (right j)
    · rfl
    · exact (h.1 ⟨i, j, e, hi, hj⟩).elim
  · intro free
    apply add_free h (left i)
    · intro k j e hk
      have eq : k = i := left_injective hk
      subst k
      exact free j e
    · intro k j _ hj
      exact (left_ne_right i j hj.symm).elim

set_option maxRecDepth 100000 in
set_option maxHeartbeats 3000000 in
theorem check_completions :
    ∀ a : Fin 7 → Bool,
      (∀ i, a i = allowedLeft (allowedRight a) i) →
        masks.any (fun m => (List.finRange 14).all (fun i => completion a i == m.testBit i.val)) =
          true := by
  decide +kernel

theorem classify {x : Assignment} (h : Maximal Independent x) :
    ∃ m ∈ masks, ∀ i : Fin 14, x i = m.testBit i.val := by
  let a : Fin 7 → Bool := fun i => x (left i)
  have same : ∀ j, x (right j) = allowedRight a j := right_forced h
  have closed : ∀ i, a i = allowedLeft (allowedRight a) i := by
    intro i
    have sameFunction : (fun j => x (right j)) = allowedRight a := funext same
    simpa only [a, sameFunction] using left_forced h i
  have whole : x = completion a := by
    funext i
    refine Fin.addCases (m := 7) (n := 7) (motive := fun k => x k = completion a k)
      (fun j => ?_) (fun j => ?_) i
    · simp only [completion, Fin.addCases_left, a]
    · simpa only [completion, Fin.addCases_right] using same j
  obtain ⟨m, hm, bits⟩ := List.any_eq_true.mp (check_completions a closed)
  refine ⟨m, hm, fun i => ?_⟩
  have bit := List.all_eq_true.mp bits i (by simp)
  rw [whole]
  simpa using bit

end PEqualNP.Outside.L_meta_18522

theorem PEqualNP.Outside.L_meta_18522 :
∀ (x1 : Fin (14 : ℕ) → Bool),   Maximal (fun (x2 : Fin (14 : ℕ) → Bool) => ¬∃ (x3 : Fin (7 : ℕ)) (x4 : Fin (7 : ℕ)), (x3 = x4 ∨ x3 = x4 + (1 : Fin (7 : ℕ)) ∨ x3 = x4 + (3 : Fin (7 : ℕ))) ∧ x2 (Fin.castAdd (7 : ℕ) x3) = Bool.true ∧ x2 (Fin.natAdd (7 : ℕ) x4) = Bool.true) x1 →     ∃       x3 ∈         have x4 : List ℕ :=           have x4 : List ℕ :=             have x4 : List ℕ := [(11778 : ℕ), (12312 : ℕ), (12944 : ℕ), (14600 : ℕ), (16256 : ℕ)];             (8488 : ℕ) :: (8722 : ℕ) :: (9250 : ℕ) :: (9632 : ℕ) :: (10250 : ℕ) :: x4;           have x5 : List ℕ := (5889 : ℕ) :: (6156 : ℕ) :: (7300 : ℕ) :: (8250 : ℕ) :: (8368 : ℕ) :: x4;           (4244 : ℕ) :: (4361 : ℕ) :: (4625 : ℕ) :: (5125 : ℕ) :: x5;         have x5 : List ℕ :=           have x5 : List ℕ := (2376 : ℕ) :: (2626 : ℕ) :: (3008 : ℕ) :: (3078 : ℕ) :: (4125 : ℕ) :: x4;           (1313 : ℕ) :: (1539 : ℕ) :: (2126 : ℕ) :: (2244 : ℕ) :: x5;         have x6 : List ℕ := (595 : ℕ) :: (720 : ℕ) :: (833 : ℕ) :: (1063 : ℕ) :: (1188 : ℕ) :: x5;         (127 : ℕ) :: (244 : ℕ) :: (361 : ℕ) :: (480 : ℕ) :: x6,       ∀ (x4 : Fin (14 : ℕ)), x1 x4 = x3.testBit ↑x4 := by
  intro x h
  exact PEqualNP.Outside.L_meta_18522.classify h
