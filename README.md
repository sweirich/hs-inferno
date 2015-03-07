A port of Francois Pottier's inferno library from OCaml to Haskell.

This translation to the world's finest imperative programming language is (so
far) fairly faithful. But buggy.

An example for core ML is in the file [test/Client.hs](test/Client.hs). This
file uses the library to implement a type inferencer as described in the
paper. 

The interface to the library is contained in
[UnifierSig.hs](Language/Inferno/UnifierSig.hs).  The requirements of the
object language types are fairly small:

* The most important part of this interface is that it requires the definition
  of a shallow type.  This shallow type must be an instance of the classes
  Typeable, Traversable and Foldable as well as a new one called `ZipM`.  This
  last class compares two shallow types and throws an exception if they
  differ.

* The output type of the elaborator must also be a member of the `Output` type
  class.

Observations
------------
* I tried very hard to make the most literal translation that I could from
  OCaml to Haskell. This means that the Haskell code is perhaps more
  imperative than is ideomatic.
  
  
* One place this was a bit ridiculuous was the treatment of fresh variable 
  generation.  The ML library can encapsulate a counter in a module, and
  generate fresh variables based on that "global" state. 
  
  The Haskell version avoids the easy `unsafePerformIO` and defines a
  freshness monad. That monad constraint means that the state can be passed
  around, marking where fresh variables are necessary. But that freshness
  monad comes with its own problems: it cannot be ST or IO.  As a result, the
  library is generic about what form of references it uses.
  
  Haskell's lack of functors means that I had to resort to type
  parameterization throughout the library. That means that the interface types
  of the solver are quite hideous.  Insead of 
  
        exist :: (Variable -> Co a) -> Co (t, a)
  
  we have to index unification variables by `m` the monad that stores their
  state, (and can generate fresh ones when needed) and the shallow structure
  that we need for unification. As coercions are about variables, that type is
  also parameterized by those two types.
  
        exist :: forall m t a. (MonadFresh m, MonadRef m, Traversable (Src t)) =>
         (Var m (Src t) -> m (Co m t a)) -> m (Co m t (t,a))
  
  Type families instead of functional dependencies means that this function
  has 3 type args instead of 5.

TODO
----
  - Replace `TRefMap` with a more efficient data structure.
  - Break out `MonadFresh` into a separate class
  - 
