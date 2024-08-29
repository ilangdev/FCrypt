import Mathlib.Tactic
import Mathlib.Algebra.Field.Basic

section

def Vector (α : Type) (n : ℕ) : Type :=
   {xs : List α // List.length xs = n}


-- Type for support a linear code
def Vec (F : Type) [Field F] (n : ℕ) := Vector F n

def v1 : Vec ℚ 3 := Subtype.mk [1, 2, 3] (by rfl)
def v2 : Vec ℚ 3 := Subtype.mk [1, 2, 4] (by rfl)

-- Vec needs to support an additive group structure
instance {F : Type} [Field F] {n : ℕ} : Zero (Vec F n) :=
  ⟨List.replicate n 0, (by rw [List.length_replicate])⟩

instance {F : Type} [Field F] {n : ℕ} : Add (Vec F n) :=
  ⟨fun v1 v2 =>  ⟨ List.zipWith (. + .) (Subtype.val v1) (Subtype.val v2),
                   ( by  rw [List.length_zipWith]; simp [min_self] ) ⟩ ⟩

instance {F : Type} [Field F] {n : ℕ} : Neg (Vec F n) :=
  ⟨fun v =>  ⟨ List.map (Neg.neg) (Subtype.val v),
             ( by rw [List.length_map]; simp ) ⟩ ⟩

instance {F : Type} [Field F] {n : ℕ} : Sub (Vec F n) :=
  ⟨fun v1 v2 =>  ⟨ List.zipWith (. - .) (Subtype.val v1) (Subtype.val v2),
                   ( by rw [List.length_zipWith]; simp [min_self] ) ⟩ ⟩

theorem zero_def {F : Type} [Field F] {n : ℕ} :
  Subtype.val (0 : Vec F n) = List.replicate n 0 := rfl

-- theorem zero_add_vec {F : Type} [Field F] {n : ℕ} :
--   ∀ (v : Vec F n), Subtype.val v = Subtype.val (v + 0)
--     | Subtype.val [] => by simp

variable {F : Type} [Field F] {n : ℕ}

def nsmul' (m: ℕ) (v : Vec F n) : Vec F n := ⟨ List.map (fun x => n * x) v.val, by sorry ⟩

instance : AddCommGroup (Vec F n) where
  zero_add := by sorry
  add_zero := by sorry
  add_assoc := by sorry
  add_comm := by sorry
  neg_add_cancel := by sorry
  sub_eq_add_neg := by sorry
  nsmul := nsmul'
  zsmul n v := zsmulRec nsmul' n v
  nsmul_zero := by sorry
  nsmul_succ := by sorry
  zsmul_zero' := by sorry
  zsmul_succ' := by sorry

end

def hamming_distance {F : Type} [LinearOrder F] (v1 v2 : List F) (d : ℕ) : ℕ :=
  match v1, v2 with
    | x :: xs, y :: ys =>
      if x == y then hamming_distance xs ys (d + 1) else hamming_distance xs ys d
    | _, _ => d

def hamming_dist {F : Type} [LinearOrder F] [Field F] {n : ℕ} (v1 v2 : Vec F n) : ℕ :=
  hamming_distance (Subtype.val v1) (Subtype.val v2) 0

#eval hamming_dist v1 v2



-- structure LinearCode {F K : Type} [Field F] [LinearOrder F] (n : ℕ)
--   where
--     code : Vec F n
--     d : ℕ
--     code_with_dist : ∀ y ∈ code, ∀ x ∈ code, hamming_dist y x ≥ d
