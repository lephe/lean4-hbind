Tests related to generalizing monadic binds and `do`-notation to universe polymorphic monads in Lean 4.

* [Main discussion thread on the Lean 4 Zulipchat](https://leanprover.zulipchat.com/#narrow/stream/270676-lean4/topic/universe.20polymorphic.20IO)

**TODO**

* A lot more examples with trickier inference situations:
  - Stress on universe inference in occurrences of `Prod` rather than `MProd`
  - Complex combinators like `for in do`, `try catch`, etc
  - Polymorphic monad operations based on eg. `[MonadRef m]`, `[MonadEnv m]`, `[MonadLift m m']`
  - "Auto-lifting"
* Generalizing the [output type](https://leanprover.zulipchat.com/#narrow/stream/270676-lean4/topic/universe.20polymorphic.20IO/near/289615681) to cover more complex bind instances
* Alternate approach: consider trying [`is_monadic`](https://leanprover.zulipchat.com/#narrow/stream/270676-lean4/topic/universe.20polymorphic.20IO/near/282613597)
