Here are some instructions on how to use the Ling tool chain.

## Requirements

If you're new to Haskell your simplest option might be to install `stack`: http://docs.haskellstack.org/en/stable/README.html#how-to-install

## Building

Once the repository is cloned, you can setup a local Haskell environment:

```
$ stack setup
```

Then to build the tool chain:

```
$ stack build
```

Finally you can run the compiler on a simple example:

```
$ stack exec Ling --seq --fuse --pretty --compile fixtures/compile/double.ll
```

The command above is type checking, apply sequencing and fusion. It finally
prints the final version in Ling and in C.

## Contributions

Various contributions can be made whether you know Haskell or not.

Beside hacking on the tool chain, you can:

* Write small programs in the language
* Submit bug reports
* Join the discussion on the evolution of the language
* Help with the documentations and tutorials
