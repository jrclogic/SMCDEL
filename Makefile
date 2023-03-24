default:
	stack build

clean:
	stack clean
	find src/ -iname *.hi -type f -print | xargs /bin/rm -f
	find src/ -iname *.o -type f -print | xargs /bin/rm -f

MCBENCHMARKS = DEMOS5 CacBDD CUDD Trans Triangle NonS5 NonS5Trans

benchmc-results.csv:
	stack bench :bench-muddychildren --benchmark-arguments "$(MCBENCHMARKS) --csv benchmc-results.csv"

todo:
	@bash -c 'grep -nr "TODO" {src,exec,test,bench}'
	@bash -c 'grep -nr "FIXME" {src,exec,test,bench}'

ACEVERSION = 1.16.0

static/ace.js:
	wget -c "https://github.com/ajaxorg/ace-builds/archive/v$(ACEVERSION).tar.gz" -O static/ace.tgz
	tar xz -C static -f static/ace.tgz ace-builds-$(ACEVERSION)/src-min-noconflict/ace.js
	mv static/ace-builds-$(ACEVERSION)/src-min-noconflict/ace.js static/ace.js
	rm -rf static/ace-builds-$(ACEVERSION)
	rm static/ace.tgz

.PHONY: default clean todo
