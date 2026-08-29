
import LeanBook.Ch6_2_OrdMonoid

-- ## DecidableOrder

-- 具体的な数値 a, b について a = b や a ≠ b が decide タクティクで証明できるように
deriving instance DecidableEq for MyNat

example : 32 + 13 ≠ 46 := by
  decide

#eval 1 ≠ 2

-- a ≤ b かどうか計算する
def MyNat.ble (a b : MyNat) : Bool :=
  match a, b with
  | 0, _ => true
  | _ + 1, 0 => false
  | a' + 1, b' + 1 => MyNat.ble a' b' -- succ を一枚剥がして再評価

#eval MyNat.ble 4 3

instance (a b : MyNat) : Decidable (a ≤ b) := by
  apply decidable_of_iff (MyNat.ble a b = true)
  guard_target =ₛ
    a.ble b = true ↔ a ≤ b -- これを示す
  sorry

set_option linter.defProp false

@[simp]
theorem MyNat.ble_zero_left (n : MyNat) :
  MyNat.ble 0 n = true := by rfl

@[simp]
theorem MyNat.ble_zero_right (n : MyNat) :
  MyNat.ble (n + 1) 0 = false := by rfl

@[simp]
theorem MyNat.ble_succ (m n : MyNat) :
  MyNat.ble (m + 1) (n + 1) = MyNat.ble m n := by rfl

-- 帰納法で記法が崩れる問題の対策
def MyNat.ble.inductAux (motive : MyNat → MyNat → Prop)
    (case1 : ∀ (n : MyNat), motive 0 n)
    (case2 : ∀ (n : MyNat), motive (n + 1) 0)
    (case3 : ∀ (m n : MyNat), motive m n → motive (m + 1) (n + 1))
    (m n : MyNat) : motive m n := by
  induction m, n using MyNat.ble.induct with
  | case1 n => apply case1
  | case2 n => apply case2
  | case3 m n h => apply case3; assumption

theorem MyNat.le_impl (m n : MyNat) : MyNat.ble m n = true ↔ m ≤ n := by
  induction m, n using MyNat.ble.inductAux with
  | case1 n =>
    simp only [ble_zero_left]
    simp only [zero_le]
  | case2 n =>
    simp only [ble_zero_right]
    simp_all only [Bool.false_eq_true, le_zero, add_eq_zero_iff_eq_zero, one_neq_zero, and_false]
  | case3 m n ih =>
    simp only [ble_succ]
    simp_all only [add_le_add_iff_right]

instance : DecidableLE MyNat := fun n m =>
  decidable_of_iff (MyNat.ble n m = true) (MyNat.le_impl n m)

example : 1 ≤ 9 := by
  decide

theorem MyNat.lt_impl (m n : MyNat) : MyNat.ble (m + 1) n ↔ m < n := by
  rw [MyNat.le_impl]
  rfl

/-- 狭義の順序関係を決定可能にする-/
instance : DecidableLT MyNat := fun n m =>
  decidable_of_iff (MyNat.ble (n + 1) m = true) (MyNat.lt_impl n m)

example : 4 < 8 := by
  decide

example : 23 < 32 ∧ 12 ≤ 24 := by
  constructor <;> decide
