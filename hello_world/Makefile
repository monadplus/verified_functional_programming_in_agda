CXX=agda

all: hello-world

hello-world: hello-world.agda
	#nix-shell --command "$(CXX) --compile $<"
	$(CXX) --compile $<
	#$(CXX) -o $@ $<

clean:
	rm -r hello-world *.o *.agdai
.PHONY: clean
