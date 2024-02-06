import Lake

open Lake DSL

package love

@[default_target]
lean_lib LoVe {
  roots := #[`LoVe]
  globs := #[Glob.submodules `LoVe]
}

require mathlib from git "https://github.com/leanprover-community/mathlib4" @ "a12f60d418e65204e80a06e18db8132fd61ec210"

-- HACK: we depend on a version of Aesop different from the version that mathlib
-- currently uses. This breaks the mathlib cache, so `lake exe cache get`
-- largely fails to download precompiled files and `lake build` takes a long
-- time as a result. Once mathlib has caught up with Aesop, we'll be able to
-- delete this line and everything will be fine again.
require aesop from git "https://github.com/JLimperg/aesop" @ "29c1f0ad4669e340b5d26c0cdad7888746048f41"
