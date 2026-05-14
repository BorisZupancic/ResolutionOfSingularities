.PHONY: all install docs test test-file clean

all: clean test docs

install: 
	sage -pip install -e . --prefix=$(HOME)/.sage/local

docs:
	PYTHONPATH=$(PWD)/src make -C docs clean html
	xdg-open docs/_build/html/index.html 2>/dev/null

TEST_FILES := $(shell git ls-files 'src/*.py' 'src/**/*.py')
test:
	PYTHONPATH=$(PWD)/src sage -t $(TEST_FILES)

test-file:
	PYTHONPATH=$(PWD)/src sage -t src/ResolutionOfSingularities/$(FILE)

clean:
	make -C docs clean
