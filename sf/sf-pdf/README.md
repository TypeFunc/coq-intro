## Coq/SoftwareFoundations/sf-pdf

This directory contains pdf versions of the sf book.

The documents sf.pdf and sf-color.pdf were created as described below.  The file
sf-solutions-wjd.pdf was created using similar commands inside the sf-solutions-wjd
directory.  Therefore, sf-solutions-wjd.pdf includes solutions to some of
the exercises in the book (some of which might be correct).

1. download the
[sf.tar.gz archive](http://www.cis.upenn.edu/~bcpierce/sf/current/sf.tar.gz) and
unpack it with

        tar xvzf sf.tar.gz

2. Enter the sf directory and compile all the source.

        make all

3. Use the `coqdoc` command to create the LaTeX version of all the chapters
   (listed in the `coqfiles.txt` file).
   
        coqdoc -t "Software Foundations" -toc --toc-depth 1 --no-lib-name --latex --files-from filelist.txt -o sf.tex

   (The options used in this command are described in a table at the bottom of this
page.)

   **Important:** the file `filelist.txt` listing all files to be included in the
   document, must exist in the working directory for the above command to
   work.
   
4. A title page can be added by manually editing the `sf.tex` file that was
   created in the previous step. Alternatively, simply include the file
   `title-authors-preamble.tex` by inserting the following line
   in the `sf.tex` file:

        \input{title-authors-preamble.tex}

   just before the line containing the `\tableofcontents` command.

5. To produce a color version of the document, in the sf.tex replaced the line

        \usepackage{coqdoc}

   with the lines

        \usepackage{xcolor}
        \usepackage[color]{coqdoc}

6. Finally, compile the tex file into a pdf document with the following command:

        pdflatex sf.tex

If you follow the above commands and encounter a problem, please [submit a new
issue](https://github.com/TypeFunc/Coq/issues) describing the problem.

The options used in the coqdoc command above have the meanings shown in the
table below:

| option            | meaning                                                        |
| ----------------- | -------------------------------------------------------------- |
|   `--no-lib-name` | Print, e.g., "Foo" instead of "Library Foo" in titles.         |
|   `-toc`          | include a table of contents                                    |
|   `--toc-depth 1` | Only include headers up to depth int in the table of contents. |
|   `--files-from coqfilelist.txt`  | include the files listed in coqfilelist        |
