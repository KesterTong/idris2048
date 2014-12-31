

var IdrisInterface = function(element) {
	this.callbacks_ = [];
	this.events_ = [];
	this.element_ = element;
	this.grid_view_ = null;

	var that = this;
	element.addEventListener('keydown', function(e) {that.on_keydown_(e)});
};


IdrisInterface.prototype.on_keydown_ = function(e) {
	if (this.callbacks_.length > 0) {
		this.callbacks_.shift()(e['keyCode']);
	} else {
		this.events_.push(e);
	}
}

IdrisInterface.prototype.get_next_event = function(callback) {
	if (this.events_.length > 0) {
		var e = this.events_.shift();
		callback(this.events_.shift());	
	} else {
		this.callbacks_.push(callback);
	}	
}

IdrisInterface.prototype.init_display = function(rows, cols) {
	if (this.grid_view_ != null) {
		console.error('init_display can only be called once');
		return;
	}
	var options = {
		rows: rows,
		cols: cols
	};
	this.grid_view_ = new GridView(this.element_, options);
}

IdrisInterface.prototype.show = function(str) {
	if (this.grid_view_ == null) {
		console.error('init_display must be called before show');
		return;
	}
	this.grid_view_.show(str);
}
