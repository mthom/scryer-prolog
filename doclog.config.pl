project_name("Scryer Prolog").
readme_file("INDEX.dj").
source_lib_folder("src/lib").
websource("https://github.com/mthom/scryer-prolog/tree/master/src/lib").
omit(["ops_and_meta_predicates.pl", "tabling"]).
learn_pages_source_folder("learn").
learn_pages_categories(["First steps", "Tutorials"]).
learn_pages([
		   page("Let's play Brisca", "Tutorials", "lets-play-brisca.dj"),
		   page("Test page", "First steps", "test-page.dj")
]).
copy_file("logo/scryer.png", "scryer.png").
copy_file("learn/Spanish_deck_Fournier.jpg", "learn/Spanish_deck_Fournier.jpg").
copy_file("learn/brisca-interactive.png", "learn/brisca-interactive.png").
