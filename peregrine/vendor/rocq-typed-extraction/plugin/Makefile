all: theory plugin
.PHONY: all

_CoqProject: _CoqProject.in _config
	cat _config > _CoqProject
	cat _CoqProject.in >> _CoqProject

_PluginProject: _PluginProject.in _config
	cat _config > _PluginProject
	cat _PluginProject.in >> _PluginProject

RocqMakefile: _CoqProject
	rocq makefile -f _CoqProject -o RocqMakefile
RocqMakefile.plugin: _PluginProject
	rocq makefile -f _PluginProject -o RocqMakefile.plugin

theory: RocqMakefile
	+@make -f RocqMakefile
	@echo "Done extracting the extraction, processing produced files!"
	./process_extraction.sh
.PHONY: plugin

plugin: theory RocqMakefile.plugin
	+@make -f RocqMakefile.plugin
.PHONY: plugin

clean: RocqMakefile
	+@make -f RocqMakefile clean
	+@make -f RocqMakefile.plugin clean
	rm -f RocqMakefile
	rm -f RocqMakefile.plugin
.PHONY: clean

clean-make:
	rm -f RocqMakefile
	rm -f RocqMakefile.Plugin
.PHONY: clean-make

install: RocqMakefile
	+@make -f RocqMakefile install
	+@make -f RocqMakefile.plugin install
.PHONY: install

uninstall: RocqMakefile
	+@make -f RocqMakefile uninstall
	+@make -f RocqMakefile.plugin uninstall
.PHONY: uninstall
