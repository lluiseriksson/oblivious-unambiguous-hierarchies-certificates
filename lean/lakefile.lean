import Lake
open Lake DSL

package «oblivious_unambiguous» where
  leanOptions := #[
    ⟨`autoImplicit, false⟩
  ]

@[default_target]
lean_lib «ObliviousUnambiguous» where
  roots := #[`ObliviousUnambiguous]
