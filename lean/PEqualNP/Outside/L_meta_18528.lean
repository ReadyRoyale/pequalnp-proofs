import Mathlib.Data.Fin.Basic
import Mathlib.Data.List.FinRange
import Mathlib.Data.Fintype.EquivFin

namespace PEqualNP.Outside.L_meta_18528

private def f (x : Fin 10 → Bool) : Bool :=
  (List.finRange 5).any fun k =>
    (x (Fin.castAdd 5 k) && x (Fin.castAdd 5 (k+1))) ||
    (x (Fin.castAdd 5 k) && x (Fin.natAdd 5 k)) ||
    (x (Fin.natAdd 5 k) && x (Fin.natAdd 5 (k+2)))

private def edges : List (Fin 10 × Fin 10) :=
  (List.finRange 5).flatMap fun k =>
    [(Fin.castAdd 5 k,Fin.castAdd 5 (k+1)),
      (Fin.castAdd 5 k,Fin.natAdd 5 k),
      (Fin.natAdd 5 k,Fin.natAdd 5 (k+2))]

private def adj (a b : Fin 10) : Prop :=
  (a,b) ∈ edges ∨ (b,a) ∈ edges

private instance (a b : Fin 10) : Decidable (adj a b) := by
  unfold adj
  infer_instance

private theorem edge_form (x : Fin 10 → Bool) :
    f x = true ↔ ∃ a b : Fin 10, adj a b ∧ x a = true ∧ x b = true := by
  have he : edges.any (fun e => x e.1 && x e.2) = f x := by
    simp [edges, f, List.any_flatMap, Bool.or_assoc]
  rw [← he, List.any_eq_true]
  constructor
  · rintro ⟨⟨a,b⟩,ab,h⟩
    simp only [Bool.and_eq_true] at h
    exact ⟨a,b,Or.inl ab,h⟩
  · rintro ⟨a,b,ab,ha,hb⟩
    rcases ab with ab | ba
    · exact ⟨(a,b),ab,by simp [ha,hb]⟩
    · exact ⟨(b,a),ba,by simp [ha,hb]⟩

private def offset (v : Fin 10) : ℕ :=
  if v.val < 5 then (9 - (2*v.val) % 5) % 5 else 9 - v.val

private def route (v i : Fin 10) : Fin 10 :=
  let k := offset v
  if v.val < 5 then
    if i.val < 5 then Fin.ofNat 10 (5 + (2*i.val+k) % 5)
    else Fin.ofNat 10 ((2*(i.val-5)+k) % 5)
  else
    if i.val < 5 then Fin.ofNat 10 ((i.val+k) % 5)
    else Fin.ofNat 10 (5 + ((i.val-5)+k) % 5)

private def back (v i : Fin 10) : Fin 10 :=
  let k := offset v
  if v.val < 5 then
    if i.val < 5 then Fin.ofNat 10 (5 + (3*(i.val+5-k)) % 5)
    else Fin.ofNat 10 ((3*(i.val-k)) % 5)
  else
    if i.val < 5 then Fin.ofNat 10 ((i.val+5-k) % 5)
    else Fin.ofNat 10 (5 + (i.val-k) % 5)

set_option maxHeartbeats 1500000 in
private theorem back_route : ∀ v i : Fin 10, back v (route v i) = i := by
  decide +kernel

set_option maxHeartbeats 1500000 in
private theorem route_back : ∀ v i : Fin 10, route v (back v i) = i := by
  decide +kernel

private theorem reaches : ∀ v : Fin 10, route v v = 9 := by decide +kernel

set_option maxHeartbeats 2500000 in
private theorem same_edges : ∀ v a b : Fin 10, adj a b ↔ adj (route v a) (route v b) := by
  decide +kernel

private def perm (v : Fin 10) : Equiv.Perm (Fin 10) :=
  ⟨route v,back v,back_route v,route_back v⟩

theorem transitive : ∀ v : Fin 10, ∃ p : Equiv.Perm (Fin 10), p v = 9 ∧
    ∀ x : Fin 10 → Bool, f (x ∘ p) = f x := by
  intro v
  refine ⟨perm v,reaches v,fun x => ?_⟩
  apply Bool.eq_iff_iff.mpr
  rw [edge_form,edge_form]
  constructor
  · rintro ⟨a,b,ab,ha,hb⟩
    exact ⟨route v a,route v b,(same_edges v a b).mp ab,ha,hb⟩
  · rintro ⟨a,b,ab,ha,hb⟩
    have ar : route v (back v a) = a := route_back v a
    have br : route v (back v b) = b := route_back v b
    have h : adj (route v (back v a)) (route v (back v b)) := by rwa [ar,br]
    refine ⟨back v a,back v b,(same_edges v _ _).mpr h,?_,?_⟩
    · change x (route v (back v a)) = true
      rwa [ar]
    · change x (route v (back v b)) = true
      rwa [br]

end PEqualNP.Outside.L_meta_18528

theorem PEqualNP.Outside.L_meta_18528 : (have x1 : (Fin (10 : ℕ) → Bool) → Bool := fun (x1 : Fin (10 : ℕ) → Bool) => (List.finRange (5 : ℕ)).any fun (x2 : Fin (5 : ℕ)) => x1 (Fin.castAdd (5 : ℕ) x2) && x1 (Fin.castAdd (5 : ℕ) (x2 + (1 : Fin (5 : ℕ)))) || x1 (Fin.castAdd (5 : ℕ) x2) && x1 (Fin.natAdd (5 : ℕ) x2) || x1 (Fin.natAdd (5 : ℕ) x2) && x1 (Fin.natAdd (5 : ℕ) (x2 + (2 : Fin (5 : ℕ)))); ∀ (x2 : Fin (10 : ℕ)), ∃ (x3 : Equiv.Perm (Fin (10 : ℕ))), x3 x2 = (9 : Fin (10 : ℕ)) ∧ ∀ (x4 : Fin (10 : ℕ) → Bool), x1 (x4 ∘ ⇑x3) = x1 x4) := PEqualNP.Outside.L_meta_18528.transitive
