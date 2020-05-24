.PHONY: all

all: output/document.pdf presentation/presentation.pdf
	isabelle build -c -v -d . DeBruijn

output/document.pdf:
	isabelle build -c -v -d . DeBruijn

presentation/presentation.pdf:
	make -C presentation

clean:
	$(CURDIR)/util/trash_heap.sh
	rm -rf output
