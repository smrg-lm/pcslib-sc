// pcslib-sc 2011
// Pitch Class Set Chain

PCSChain : List {
	var <norm;
	var <candList;

	*new { arg norm;
		var ret = super.new;
		norm !? { ret.norm = norm };
		^ret;
	}

	norm_ { arg pcs;
		if(norm.isNil, {
			norm = pcs;
		}, {
			if(norm.cardinal == pcs.cardinal, {
				norm = pcs;
			}, {
				Error(
					"PCSChain: new norm must have the same cardinal number"
				).throw;
			})
		});
	}

	candidates { arg postList = true;
		var pcs, normName, subsets;

		if(this.isEmpty, {
			candList = norm.binpart;
		}, {
			candList = [];
			normName = this.norm.name;
			pcs = this.last;
			subsets = (0..11).as(PCS).subsets(this.norm.cardinal - pcs.cardinal);
			subsets.do({ arg i;
				if((pcs union: i).name == normName, {
					candList = candList.add([i]);
				});
			});
		});
		this.prSortCandidates;

		if(postList, {
			if(this.isEmpty, {
				candList.do({ arg i, j;
					"cand %: %".format(j, i).postln;
				});
			}, {
				candList.flat.do({ arg i, j;
					"cand %: %, score: %".format(j, i, this.prScore(i)).postln;
				});
			});
		});
	}

	prSortCandidates {
		candList.sort({ arg a, b;
			var i, noBreak, ret = false;
			a = a.at(0).asArray;
			b = b.at(0).asArray;

			if(a.size < b.size, { ret = true });
			if(a.size == b.size, {
				i = 0;
				noBreak = true;
				while({ (i < a.size) and: noBreak }, {
					case({ a.at(i) < b.at(i) }, {
						ret = true; noBreak = false;
						}, { a.at(i) > b.at(i) }, {
							ret = false; noBreak = false;
					});
					i = i + 1;
				});
			});

			ret;
		});
	}

	addCand { arg index, postNext = false;
		if(candList.isNil, {
			("PCSChain: candidates were not initialized, now they are").warn;
			this.candidates;
			^this;
		});

		candList.at(index).do({ arg pcs;
			this.add(pcs);
		});

		this.candidates(postNext);
	}

	scores {
		var ret;

		if(this.notEmpty, {
			ret = candList.flat.collect({ arg i;
				this.prScore(i);
			});
		});

		^ret;
	}

	prScore { arg cand;
		var res, continue, list, pclist, index;

		//pcs.collect makes something weird
		res = cand.asArray.collect({ arg pc1;
			var pcs, pc2;

			continue = true;
			list = this.reverse.iter;
			index = this.size;

			while({ (pcs = list.next).notNil and: continue }, {
				index = index - 1;
				pclist = pcs.iter;
				while({ (pc2 = pclist.next).notNil and: continue }, {
					if(pc1 == pc2, {
						index = index + 2;
						continue = false;
					});
				});
			});
			index;
		});

		^(this.size - res).sum / (this.size * cand.cardinal);
	}

	embedInStream { arg inval;
		this.do({ arg pcs; inval = pcs.embedInStream(inval) });
	}

	asStream {
		^Routine({ arg inval; this.embedInStream(inval) })
	}
}
