.PHONY: shadow-server
shadow-server:
	npx shadow-cljs server

.PHONY: shadow-watch
shadow-watch:
	shadow-cljs watch app
