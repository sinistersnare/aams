# Abstract Machines ... Abstracted! #

I wrote about what abstraction machines are
[on my blog here](https://drs.is/post/abstract-machines/).
This repo implements an abstract machine: a `time-stamped CESK*` Machine.
I then use concepts from the
['Abstracting Abstract Machines' paper](http://matt.might.net/papers/vanhorn2010abstract.pdf)
To create a static-analysis of it.

* `latex/`: Formalizations of these machines in LaTeX computer-sciencese.
* `src/`: Implementation of the formalizations in both `Racket` and `Rust`.
* `examples/`: Example scheme programs that the machines should accept.

The formalizations of these machines are available in the `latex/` directory.

I have both Racket and Rust implementations of the machine. See `src/` for those.

In the `examples/` directory are some basic scheme programs accepted by these machines.


## Running ##

To run the Rust code

```bash
cargo run -- examples/basic.scm # to run a scheme file
cargo run # to start a REPL
```

For Racket, load the machine up in your Racket environment of choice,
and use the `evaluate` function to run a program.

```racket
> (evaluate '(prim + 3 4 (let ([x 6] [y 10]) (prim + x y))))
```

## Abstrat Interpretation ##

Abstract Interpretation is a style of static-analysis that attempts
to run the program in a decidably computable, sound way
(No we did not have to solve the halting problem).
By computing using abstract values insted of concrete values,
we can over-approximate program behavior.

'Abstracting Abstract Machines' shows how we can use Abstract Machines
to more easily create abstract interpreters. Thats what we are doing here,
We first implement a concrete machine, and then we lift it into abstract-space
to create an analysis.

## Future Work / TODO ##

I also plan on implementing Delimited Continuations instead of one-shot
continuations. DCs are much more efficient and powerful.
Hopefully after I get the analysis finished, I can start on this!

I want to extend the machines semantics to cover most of
[SinScheme](https://github.com/sinistersnare/SinScheme).
That way, I can do a static analysis of it, and perform real optimizations
on it. This is a a stretch goal, but I think its doable!

## License ##

MIT license! Enjoy!

Let me know if you use/enjoy this project, I would be very happy to hear it.
