// pcslib-sc 2011
// Combinatory Matrix

PCSMatrix {
	var <type;
	var <matrix;
	var <vnorm, <hnorm;

	*roman { arg norm;
		^super.new.initMatrix(norm, nil, \roman);
	}

	*t1a { arg norm;
		^super.new.initMatrix(norm, nil, \t1a);
	}

	*t1b { arg norm;
		^super.new.initMatrix(norm, nil, \t1b);
	}

	*t2 { arg hnorm, vnorm;
		^super.new.initMatrix(hnorm, vnorm, \t2);
	}

	*fromChain { arg pcsChain, normParts = 2;
		^super.new.initMatrix(pcsChain.asArray.clump(normParts), nil, \chain);
	}

	*opcy { arg norm, op;
		^super.new.initOpcyMatrix(norm, op, \opcy);
	}

	initMatrix { arg hn, vn, t;
		matrix = [];
		type = t;

		if(hn.class == PCS, {
			hn = hn.asArray.clump(1).collect({ arg i; i.as(PCS) });
		});
		if(vn.class == PCS, {
			vn = vn.asArray.clump(1).collect({ arg i; i.as(PCS) });
		});

		switch(type,
			\roman, {
				hnorm = vnorm = hn;
				matrix = hnorm.size.collect({ arg i;
					hnorm.rotate(i.neg);
				});
			},
			\t1a, {
				hnorm = vnorm = hn;
				matrix = hnorm.collect({ arg i;
					hnorm.collect({ arg j;
						(j.asArray + i.asArray).as(PCS);
					});
				});
			},
			\t1b, {
				hnorm = vnorm = hn;
				matrix = hnorm.collect({ arg i;
					hnorm.collect({ arg j;
						(j.asArray + i.i.asArray).as(PCS);
					});
				});
			},
			\t2, {
				hnorm = hn;
				vnorm = vn ? hn;
				matrix = vnorm.collect({ arg i;
					hnorm.collect({ arg j;
						(j.asArray + i.asArray).as(PCS);
					});
				});
			},
			\chain, {
				matrix = hn.collect({ arg i, j;
					(i ++ PCS[].dup(hn.size - i.size)).rotate(j);
				});
				hnorm = hn.at(0);
				vnorm = matrix.flop.at(0).reject(_.isEmpty);
			}
		);
	}

	initOpcyMatrix { arg norm, op, t;
		var transp, size;

		switch(op.asSymbol,
			'T2/A', {
				transp = 2;
				size = 6;
			},
			'T3/9', {
				transp = 3;
				size = 4;
			},
			'T4/8', {
				transp = 4;
				size = 3;
			},
			'T6/TI', {
				transp = 6;
				size = 2;
			},
			{ Error("PCSMatrix invalid op").throw; }
		);

		matrix = [];
		type = (t ++ " " ++ op).asSymbol;
		hnorm = vnorm = norm;

		if(norm.class == PCS, {
			matrix = size.collect({ arg i;
				var ret;
				ret = ([norm] ++ PCS[].dup(size - 1)).rotate(i);
				norm = norm.t(transp);
				ret;
			});
		}, {
			matrix = size.collect({ arg i;
				var ret;
				ret = (norm ++ PCS[].dup(size - norm.size)).rotate(i);
				norm = norm.collect(_.t(transp));
				ret;
			});
		});
	}

	/* from Matrix
	printOn { arg stream;
		if (stream.atLimit) { ^this };
		stream << this.class.name << "[ " ;
		matrix.do({ arg row, i;
			if (stream.atLimit) { ^this };
			if (i != 0, { stream.comma; });
			stream << "\n";
			stream.tab;
			row.printOn(stream);
		});
		stream << "\n";
		stream << " ]" ;
	}
	*/
}

