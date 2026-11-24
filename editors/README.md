# Editor support

## Vim / Neovim

Syntax highlighting, comment settings, and `:make` with errors in the quickfix list.

```
# Neovim
mkdir -p ~/.config/nvim/after && cp -r editors/vim/* ~/.config/nvim/after/
# Vim
mkdir -p ~/.vim/after && cp -r editors/vim/* ~/.vim/after/
```

Then open a `.ken` file and run `:make`. `:copen` lists the problems; `:cnext` jumps between them.
Ken must be on your `PATH` (`cargo install --path .`).
