# Abstract Machines ... Abstracted! #

Hi these are supposed to be implementations of AM's from the AAM paper.

http://matt.might.net/papers/vanhorn2010abstract.pdf

Here are the (some?) of the machines to implement. Most of them I haven't implemented yet.

`CEK` is the simplest here (Control, Environment, Kontinuation),
`CESK` adds a Store, to remove recursion in the Environment
`CESK*` now allocates the Kontinuations in the Store.
`CESKt*` adds a time-stamp to `CESK*`, to abstract GC use.
`aCESKt*` abstracted `CESKt*`, for use in static analysis.

## What is an Abstract Machine? ##

Abstract Machines are a formalism of interpreters of programming languages,
using Computer Science fundamentals. Computer science can be done without
a computer! This is how programming languages are theorized sans computer.

An AM takes a state, processes it, and returns a new state.
If the machine is run over and over until a fixed point is reached,
we can compute the value of the program.

For example, the CEK machine has 3 parts to its state (hence the name).
By providing the Control, Environment, and Kontinuation to the machine,
a new CEK is produced, with which we can run the machine again.

## What happens when you A-ify an AM? ##

An Abstract Machine will produce a value given a program.
But during the static-analysis phase of a compiler, we can not 
simply run the program, as we dont have the necessary inputs.

By abstracting an abstract machine we can theorize possible inputs
and outputs to a program. Then, we can use these possible inputs and
outputs to inform an optimization.

## License ##

MIT license! Enjoy!
