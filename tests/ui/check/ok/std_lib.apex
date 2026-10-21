theorem g1(): nat_gcd(12, 18) = 6 := by { rfl }
theorem p1(): nat_pow(2, 10) = 1024 := by { rfl }
theorem a1(): array_size(array_push(array_push(array_empty(), 1), 2)) = 2 := by { rfl }
theorem a2(): array_get(array_set(array_of_list([1, 2, 3]), 1, 9), 1) = Option.Some(9) := by { rfl }
theorem m1(): map_get(map_insert(map_insert(map_empty(), 1, 10), 2, 20), 1) = Option.Some(10) := by { rfl }
