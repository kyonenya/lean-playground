-- 依存型理論 - Theorem Proving in Lean 4 日本語訳
-- https://aconite-ac.github.io/theorem_proving_in_lean4_ja/dependent_type_theory.html

-- # 単純型理論
def m: Nat := 1
def b1: Bool := true
def b2: Bool := false
def b3: Bool := b1 && b2

#check m
#check b1 && b2
#check b1 || b2
-- #check b1 && m

#eval m + m
#eval b3

#check Nat → Nat
#check Nat -> Nat

#eval Nat.succ 2
#eval Nat.add 2 3
#eval (5, 9).2  -- 9

#check Nat.add 2  -- Nat -> Nat
#check Nat.add  -- Nat -> Nat -> Nat

#check (3, 5)  -- Nat × Nat

def list: Nat × Nat := (3, 5)

#eval list.1  -- 3
-- #check list.3  -- it must be between 1 and 2

#check Nat.add  -- Nat → (Nat → Nat)
#check (Nat -> Nat) -> Nat  -- (Nat → Nat) → Nat

#check ((3, 2), 3)  -- (Nat × Nat) × Nat
#check (3, (2, 3))  -- Nat × Nat × Nat

-- # 項としての型
#check Nat × Nat  -- Type

def hoc: Type := Nat -> Nat -> Nat

def α : Type := hoc -> Nat -> Nat

#check Type  -- Type 1
#check Type 1  -- Type 2
