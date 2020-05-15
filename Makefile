check:
	ghc -dynamic --make -isrc src/Tests/ExtendCheck.hs -main-is Tests.ExtendCheck.main && ./src/Tests/ExtendCheck

clean:
	find src -name '*.o' -exec rm {} \;
	find src -name '*.hi' -exec rm {} \;
	rm src/Tests/ExtendCheck
