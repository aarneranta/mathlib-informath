import Mathlib

/-- The sum of the first n odd numbers. -/
def oddSum : ℕ → ℕ
  | 0 => 0
  | n + 1 => oddSum n + (2 * n + 1)

theorem prime_two' : Nat.Prime 2 := Nat.prime_two

theorem dvd_mul_self' (a b : ℕ) (h : a ∣ b) : a ∣ b * b := Dvd.dvd.mul_right h b

theorem mul_comm_group {G : Type*} [CommGroup G] (a b : G) : a * b = b * a := mul_comm a b

theorem cast_le' (m n : ℕ) (h : m ≤ n) : (m : ℝ) ≤ n := Nat.cast_le.mpr h

theorem mem_inter' {α : Type*} (s t : Set α) (x : α) (hs : x ∈ s) (ht : x ∈ t) : x ∈ s ∩ t :=
  ⟨hs, ht⟩

theorem even_or_odd' (n : ℕ) : Even n ∨ Odd n := Nat.even_or_odd n
