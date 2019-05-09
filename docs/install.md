# How to get it?

### Getting it working: brief version
```bash
$ git clone git@github.com:leanprover-community/lean-perfectoid-spaces.git
$ cd lean-perfectoid-spaces
/lean-perfectoid-spaces$ leanpkg configure
/lean-perfectoid-spaces$ update-mathlib
/lean-perfectoid-spaces$ leanpkg build
```
Cut'n'paste-friendly version:
```
git clone https://github.com/leanprover-community/lean-perfectoid-spaces
cd lean-perfectoid-spaces
leanpkg configure
update-mathlib
leanpkg build
```

### Getting it working: longer version

A brief guide to compiling the library on your machine:

1) Install Lean and Visual Studio Code following, for example, [this guide](https://github.com/leanprover-community/mathlib/blob/master/docs/elan.md)

2) Clone the project:

```
git clone git@github.com:leanprover-community/lean-perfectoid-spaces.git
```

This will create a new directory `lean-perfectoid-spaces`.

3) Build the project by typing `leanpkg build` in the `lean-perfectoid-spaces` directory.

4) Open the `lean-perfectoid-spaces` directory in Visual Studio Code.

5) That's it.
