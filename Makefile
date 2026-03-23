all: algebra/main.pdf
	latexmk -pdf main


algebra/main.pdf:
	typst compile algebra/main.typ
