.PHONY: shadow-server
shadow-server:
	npx shadow-cljs server

.PHONY: shadow-watch
shadow-watch:
	shadow-cljs watch app

.PHONY: build-tailwind
build-tailwing:
	npx tailwindcss build tailwind/main.css -o resources/public/compiled/main.css
