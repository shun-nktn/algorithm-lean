def binary_pow_with_proof (a b : Nat) : { n : Nat // n = a ^ b} :=
  match hb : b with
  | 0      => ⟨1, by simp⟩
  | b' + 1 =>
    match ha : a with
    | 0 => ⟨0, by simp⟩
    | a' + 1 =>
      let ⟨pow', proof'⟩ := binary_pow_with_proof (a' + 1) (b / 2)
      if h' : b % 2 = 0 then
        ⟨pow' ^ 2, by
          have hcancel : b / 2 * 2 = b := by
            rw [@Nat.div_mul_self_eq_mod_sub_self]
            rw [h']
            rw [Nat.sub_zero]
          rw [proof']
          rw [← Nat.pow_mul]
          rw [hcancel]
          rw [hb]
        ⟩
      else
        ⟨pow' ^ 2 * a, by
          have hmod : b % 2 = 1 := by
            rw [@Nat.mod_two_eq_one_iff_testBit_zero]
            rw [← Bool.not_eq_false]
            rw [← @Nat.mod_two_eq_zero_iff_testBit_zero]
            exact h'
          have hcancel : b / 2 * 2 = b - 1 := by
            rw [@Nat.div_mul_self_eq_mod_sub_self]
            rw [hmod]
          rw [proof']
          rw [← Nat.pow_mul]
          rw [hcancel]
          rw [Nat.sub_eq_of_eq_add hb]
          rw [ha]
          rw [← Nat.pow_succ]
        ⟩

def binary_pow : Nat → Nat → Nat := fun a b => (binary_pow_with_proof a b).val
